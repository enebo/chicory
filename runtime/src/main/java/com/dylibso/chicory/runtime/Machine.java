package com.dylibso.chicory.runtime;

import static com.dylibso.chicory.runtime.Module.computeConstantValue;
import static com.dylibso.chicory.wasm.types.Value.REF_NULL_VALUE;

import com.dylibso.chicory.runtime.exceptions.WASMRuntimeException;
import com.dylibso.chicory.wasm.exceptions.ChicoryException;
import com.dylibso.chicory.wasm.types.ElemElem;
import com.dylibso.chicory.wasm.types.ElemFunc;
import com.dylibso.chicory.wasm.types.ElemType;
import com.dylibso.chicory.wasm.types.FunctionType;
import com.dylibso.chicory.wasm.types.Instruction;
import com.dylibso.chicory.wasm.types.MutabilityType;
import com.dylibso.chicory.wasm.types.OpCode;
import com.dylibso.chicory.wasm.types.Value;
import com.dylibso.chicory.wasm.types.ValueType;
import java.util.ArrayDeque;
import java.util.List;

/**
 * This is responsible for holding and interpreting the Wasm code.
 */
class Machine {

    private final MStack stack;

    private final ArrayDeque<StackFrame> callStack;

    private final Instance instance;

    public Machine(Instance instance) {
        this.instance = instance;
        stack = new MStack();
        this.callStack = new ArrayDeque<>();
    }

    public Value[] call(int funcId, Value[] args, boolean popResults) throws ChicoryException {
        return call(stack, instance, callStack, funcId, args, null, popResults);
    }

    public static Value[] call(
            MStack stack,
            Instance instance,
            ArrayDeque<StackFrame> callStack,
            int funcId,
            Value[] args,
            FunctionType callType,
            boolean popResults)
            throws ChicoryException {

        var typeId = instance.functionType(funcId);
        var type = instance.type(typeId);

        if (callType != null) {
            verifyIndirectCall(type, callType);
        }

        var func = instance.function(funcId);
        if (func != null) {
            callStack.push(
                    new StackFrame(func.instructions(), instance, funcId, args, func.localTypes()));
            eval(stack, instance, callStack);
        } else {
            callStack.push(new StackFrame(instance, funcId, args, List.of()));
            var imprt = instance.imports().index()[funcId];
            if (imprt == null) {
                throw new ChicoryException("Missing host import, number: " + funcId);
            }

            switch (imprt.type()) {
                case FUNCTION:
                    var hostFunc = ((HostFunction) imprt).handle();
                    var results = hostFunc.apply(instance, args);
                    // a host function can return null or an array of ints
                    // which we will push onto the stack
                    if (results != null) {
                        for (var result : results) {
                            stack.push(result);
                        }
                    }
                    break;
                case GLOBAL:
                    stack.push(((HostGlobal) imprt).value());
                    break;
                default:
                    throw new ChicoryException("Not implemented");
            }
        }

        if (!callStack.isEmpty()) {
            callStack.pop();
        }

        if (!popResults) {
            return null;
        }

        if (type.returns().length == 0) return null;
        if (stack.size() == 0) return null;

        var totalResults = type.returns().length;
        var results = new Value[totalResults];
        for (var i = totalResults - 1; i >= 0; i--) {
            results[i] = stack.pop();
        }
        return results;
    }

    interface ExecuteInstruction {
        void execute(
                StackFrame frame,
                MStack stack,
                Instance instance,
                ArrayDeque<StackFrame> callStack,
                Instruction instruction,
                long[] operands)
                throws ChicoryException;
    }

    static ExecuteInstruction[] instructions = new ExecuteInstruction[OpCode.values().length];

    static {
        instructions[OpCode.UNREACHABLE.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    throw new TrapException("Trapped on unreachable instruction", callStack);
                };
        instructions[OpCode.NOP.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    // do nothing
                };
        instructions[OpCode.LOOP.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    frame.isControlFrame = true;
                    frame.registerStackSize(stack);
                };
        instructions[OpCode.BLOCK.ordinal()] = instructions[OpCode.LOOP.ordinal()];
        instructions[OpCode.IF.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    frame.isControlFrame = false;
                    frame.registerStackSize(stack);
                    var predValue = stack.pop();
                    frame.jumpTo(
                            predValue.asInt() == 0
                                    ? instruction.labelFalse()
                                    : instruction.labelTrue());
                };
        instructions[OpCode.ELSE.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    prepareControlTransfer(frame, stack, false);
                    frame.jumpTo(instruction.labelTrue());
                };
        instructions[OpCode.BR.ordinal()] = instructions[OpCode.ELSE.ordinal()];
        instructions[OpCode.BR_IF.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var pred = prepareControlTransfer(frame, stack, true).asInt();

                    frame.jumpTo(pred == 0 ? instruction.labelFalse() : instruction.labelTrue());
                };
        instructions[OpCode.BR_TABLE.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var pred = prepareControlTransfer(frame, stack, true).asInt();

                    if (pred < 0 || pred >= instruction.labelTable().length - 1) {
                        // choose default
                        frame.jumpTo(instruction.labelTable()[instruction.labelTable().length - 1]);
                    } else {
                        frame.jumpTo(instruction.labelTable()[pred]);
                    }
                };
        instructions[OpCode.CALL_INDIRECT.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tableIdx = (int) operands[1];
                    var table = instance.table(tableIdx);
                    if (table == null) { // imported table
                        table = instance.imports().table(tableIdx).table();
                    }
                    var typeId = (int) operands[0];
                    var type = instance.type(typeId);
                    int funcTableIdx = stack.pop().asInt();
                    int funcId = table.ref(funcTableIdx).asFuncRef();
                    if (funcId == REF_NULL_VALUE) {
                        throw new ChicoryException("uninitialized element " + funcTableIdx);
                    }
                    // given a list of param types, let's pop those params off the stack
                    // and pass as args to the function call
                    var args = extractArgsForParams(stack, type.params());
                    call(stack, instance, callStack, funcId, args, type, false);
                };
        instructions[OpCode.DROP.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    stack.pop();
                };
        instructions[OpCode.SELECT.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var pred = stack.pop().asInt();
                    var b = stack.pop();
                    var a = stack.pop();

                    stack.push(pred == 0 ? b : a);
                };
        instructions[OpCode.LOCAL_GET.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    stack.push(frame.local((int) operands[0]));
                };
        instructions[OpCode.LOCAL_SET.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    frame.setLocal((int) operands[0], stack.pop());
                };
        instructions[OpCode.LOCAL_TEE.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    frame.setLocal((int) operands[0], stack.peek());
                };
        instructions[OpCode.GLOBAL_GET.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    int idx = (int) operands[0];
                    var val = instance.readGlobal(idx);
                    if (val == null) {
                        val = instance.imports().global(idx).value();
                    }
                    stack.push(val);
                };
        instructions[OpCode.GLOBAL_SET.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var id = (int) operands[0];
                    var mutabilityType =
                            (instance.globalInitializer(id) == null)
                                    ? instance.imports().global(id).mutabilityType()
                                    : instance.globalInitializer(id);
                    if (mutabilityType == MutabilityType.Const) {
                        throw new RuntimeException("Can't call GLOBAL_SET on immutable global");
                    }
                    var val = stack.pop();
                    instance.writeGlobal(id, val);
                };
        instructions[OpCode.TABLE_GET.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var idx = (int) operands[0];
                    var table = instance.table(idx);
                    if (table == null) {
                        table = instance.imports().table(idx).table();
                    }
                    var i = stack.pop().asInt();
                    if (i < 0 || i >= table.limits().max() || i >= table.size()) {
                        throw new WASMRuntimeException("out of bounds table access");
                    }
                    stack.push(table.ref(i));
                };
        instructions[OpCode.TABLE_SET.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var idx = (int) operands[0];
                    var table = instance.table(idx);
                    if (table == null) {
                        table = instance.imports().table(idx).table();
                    }
                    var value = stack.pop().asExtRef();
                    var i = stack.pop().asInt();
                    table.setRef(i, value);
                };
        // TODO signed and unsigned are the same right now
        instructions[OpCode.I32_LOAD.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var ptr = (int) (operands[1] + stack.pop().asInt());
                    var val = instance.memory().readI32(ptr);
                    stack.push(val);
                };
        instructions[OpCode.I64_LOAD.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var ptr = (int) (operands[1] + stack.pop().asInt());
                    var val = instance.memory().readI64(ptr);
                    stack.push(val);
                };
        instructions[OpCode.F32_LOAD.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var ptr = (int) (operands[1] + stack.pop().asInt());
                    var val = instance.memory().readF32(ptr);
                    stack.push(val);
                };
        instructions[OpCode.F64_LOAD.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var ptr = (int) (operands[1] + stack.pop().asInt());
                    var val = instance.memory().readF64(ptr);
                    stack.push(val);
                };
        instructions[OpCode.I32_LOAD8_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var ptr = (int) (operands[1] + stack.pop().asInt());
                    var val = instance.memory().readI8(ptr);
                    stack.push(val);
                };
        instructions[OpCode.I64_LOAD8_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var ptr = (int) (operands[1] + stack.pop().asInt());
                    var val = instance.memory().readI8(ptr);
                    // TODO a bit hacky
                    stack.push(Value.i64(val.asInt()));
                };
        instructions[OpCode.I32_LOAD8_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var ptr = (int) (operands[1] + stack.pop().asInt());
                    var val = instance.memory().readU8(ptr);
                    stack.push(val);
                };
        instructions[OpCode.I64_LOAD8_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var ptr = (int) (operands[1] + stack.pop().asInt());
                    var val = instance.memory().readU8(ptr);
                    // TODO a bit hacky
                    stack.push(Value.i64(val.asInt()));
                };
        instructions[OpCode.I32_LOAD16_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var ptr = (int) (operands[1] + stack.pop().asInt());
                    var val = instance.memory().readI16(ptr);
                    stack.push(val);
                };
        instructions[OpCode.I64_LOAD16_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var ptr = (int) (operands[1] + stack.pop().asInt());
                    var val = instance.memory().readI16(ptr);
                    // TODO this is a bit hacky
                    stack.push(Value.i64(val.asInt()));
                };
        instructions[OpCode.I32_LOAD16_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var ptr = (int) (operands[1] + stack.pop().asInt());
                    var val = instance.memory().readU16(ptr);
                    stack.push(val);
                };
        instructions[OpCode.I64_LOAD16_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var ptr = (int) (operands[1] + stack.pop().asInt());
                    var val = instance.memory().readU16(ptr);
                    // TODO this is a bit hacky
                    stack.push(Value.i64(val.asInt()));
                };
        instructions[OpCode.I64_LOAD32_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var ptr = (int) (operands[1] + stack.pop().asInt());
                    var val = instance.memory().readI32(ptr);
                    // TODO this is a bit hacky
                    stack.push(Value.i64(val.asInt()));
                };
        instructions[OpCode.I64_LOAD32_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var ptr = (int) (operands[1] + stack.pop().asInt());
                    var val = instance.memory().readU32(ptr);
                    stack.push(val);
                };
        instructions[OpCode.I32_STORE.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var value = stack.pop().asInt();
                    var ptr = (int) (operands[1] + stack.pop().asInt());
                    instance.memory().writeI32(ptr, value);
                };
        instructions[OpCode.I32_STORE16.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var value = stack.pop().asShort();
                    var ptr = (int) (operands[1] + stack.pop().asInt());
                    instance.memory().writeShort(ptr, value);
                };
        instructions[OpCode.I64_STORE16.ordinal()] = instructions[OpCode.I32_STORE16.ordinal()];
        instructions[OpCode.I64_STORE.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var value = stack.pop().asLong();
                    var ptr = (int) (operands[1] + stack.pop().asInt());
                    instance.memory().writeLong(ptr, value);
                };
        instructions[OpCode.F32_STORE.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var value = stack.pop().asFloat();
                    var ptr = (int) (operands[1] + stack.pop().asInt());
                    instance.memory().writeF32(ptr, value);
                };
        instructions[OpCode.F64_STORE.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var value = stack.pop().asDouble();
                    var ptr = (int) (operands[1] + stack.pop().asInt());
                    instance.memory().writeF64(ptr, value);
                };
        instructions[OpCode.MEMORY_GROW.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var size = stack.pop().asInt();
                    var nPages = instance.memory().grow(size);
                    stack.push(Value.i32(nPages));
                };
        instructions[OpCode.MEMORY_FILL.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var memidx = (int) operands[0];
                    if (memidx != 0) {
                        throw new WASMRuntimeException(
                                "We don't support multiple memories just yet");
                    }
                    var size = stack.pop().asInt();
                    var val = stack.pop().asByte();
                    var offset = stack.pop().asInt();
                    var end = (size + offset);
                    instance.memory().fill(val, offset, end);
                };
        instructions[OpCode.I32_STORE8.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var value = stack.pop().asByte();
                    var ptr = (int) (operands[1] + stack.pop().asInt());
                    instance.memory().writeByte(ptr, value);
                };
        instructions[OpCode.I64_STORE8.ordinal()] = instructions[OpCode.I32_STORE8.ordinal()];
        instructions[OpCode.I64_STORE32.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var value = stack.pop().asLong();
                    var ptr = (int) (operands[1] + stack.pop().asInt());
                    instance.memory().writeI32(ptr, (int) value);
                };
        instructions[OpCode.MEMORY_SIZE.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) ->
                        stack.push(Value.i32(instance.memory().pages()));
        // TODO 32bit and 64 bit operations are the same for now
        instructions[OpCode.I32_CONST.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) ->
                        stack.push(Value.i32((int) operands[0]));
        instructions[OpCode.I64_CONST.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) ->
                        stack.push(Value.i64(operands[0]));
        instructions[OpCode.F32_CONST.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) ->
                        stack.push(Value.f32(operands[0]));
        instructions[OpCode.F64_CONST.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) ->
                        stack.push(Value.f64(operands[0]));
        instructions[OpCode.I32_EQ.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asInt();
                    var b = stack.pop().asInt();
                    stack.push(a == b ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.I64_EQ.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asLong();
                    var b = stack.pop().asLong();
                    stack.push(a == b ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.I32_NE.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asInt();
                    var b = stack.pop().asInt();
                    stack.push(a == b ? Value.FALSE : Value.TRUE);
                };
        instructions[OpCode.I64_NE.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asLong();
                    var b = stack.pop().asLong();
                    stack.push(a == b ? Value.FALSE : Value.TRUE);
                };
        instructions[OpCode.I32_EQZ.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asInt();
                    stack.push(a == 0 ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.I64_EQZ.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asLong();
                    stack.push(a == 0L ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.I32_LT_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asInt();
                    var a = stack.pop().asInt();
                    stack.push(a < b ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.I32_LT_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asInt();
                    var a = stack.pop().asInt();
                    stack.push(Integer.compareUnsigned(a, b) < 0 ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.I64_LT_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asLong();
                    var a = stack.pop().asLong();
                    stack.push(a < b ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.I64_LT_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asLong();
                    var a = stack.pop().asLong();
                    stack.push(Long.compareUnsigned(a, b) < 0 ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.I32_GT_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asInt();
                    var a = stack.pop().asInt();
                    stack.push(a > b ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.I32_GT_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asInt();
                    var a = stack.pop().asInt();
                    stack.push(Integer.compareUnsigned(a, b) > 0 ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.I64_GT_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asLong();
                    var a = stack.pop().asLong();
                    stack.push(a > b ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.I64_GT_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asLong();
                    var a = stack.pop().asLong();
                    stack.push(Long.compareUnsigned(a, b) > 0 ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.I32_GE_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asInt();
                    var a = stack.pop().asInt();
                    stack.push(a >= b ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.I32_GE_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asInt();
                    var a = stack.pop().asInt();
                    stack.push(Integer.compareUnsigned(a, b) >= 0 ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.I64_GE_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asLong();
                    var a = stack.pop().asLong();
                    stack.push(a >= b ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.I64_GE_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asLong();
                    var a = stack.pop().asLong();
                    stack.push(Long.compareUnsigned(a, b) >= 0 ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.I32_LE_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asInt();
                    var a = stack.pop().asInt();
                    stack.push(a <= b ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.I32_LE_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asInt();
                    var a = stack.pop().asInt();
                    stack.push(Integer.compareUnsigned(a, b) <= 0 ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.I64_LE_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asLong();
                    var a = stack.pop().asLong();
                    stack.push(a <= b ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.I64_LE_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asLong();
                    var a = stack.pop().asLong();
                    stack.push(Long.compareUnsigned(a, b) <= 0 ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.F32_EQ.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asFloat();
                    var b = stack.pop().asFloat();
                    stack.push(a == b ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.F64_EQ.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asDouble();
                    var b = stack.pop().asDouble();
                    stack.push(a == b ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.I32_CLZ.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asInt();
                    var count = Integer.numberOfLeadingZeros(tos);
                    stack.push(Value.i32(count));
                };
        instructions[OpCode.I32_CTZ.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    ;
                    var tos = stack.pop().asInt();
                    var count = Integer.numberOfTrailingZeros(tos);
                    stack.push(Value.i32(count));
                };
        instructions[OpCode.I32_POPCNT.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asInt();
                    var count = Integer.bitCount(tos);
                    stack.push(Value.i32(count));
                };
        instructions[OpCode.I32_ADD.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asInt();
                    var b = stack.pop().asInt();
                    stack.push(Value.i32(a + b));
                };
        instructions[OpCode.I64_ADD.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asLong();
                    var b = stack.pop().asLong();
                    stack.push(Value.i64(a + b));
                };
        instructions[OpCode.I32_SUB.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asInt();
                    var b = stack.pop().asInt();
                    stack.push(Value.i32(b - a));
                };
        instructions[OpCode.I64_SUB.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asLong();
                    var b = stack.pop().asLong();
                    stack.push(Value.i64(b - a));
                };
        instructions[OpCode.I32_MUL.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asInt();
                    var b = stack.pop().asInt();
                    stack.push(Value.i32(a * b));
                };
        instructions[OpCode.I64_MUL.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asLong();
                    var b = stack.pop().asLong();
                    stack.push(Value.i64(a * b));
                };
        instructions[OpCode.I32_DIV_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asInt();
                    var a = stack.pop().asInt();
                    if (a == Integer.MIN_VALUE && b == -1) {
                        throw new WASMRuntimeException("integer overflow");
                    }
                    stack.push(Value.i32(a / b));
                };
        instructions[OpCode.I32_DIV_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asUInt();
                    var a = stack.pop().asUInt();
                    stack.push(Value.i32(a / b));
                };
        instructions[OpCode.I64_DIV_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asLong();
                    var a = stack.pop().asLong();
                    if (a == Long.MIN_VALUE && b == -1L) {
                        throw new WASMRuntimeException("integer overflow");
                    }
                    stack.push(Value.i64(a / b));
                };
        instructions[OpCode.I64_DIV_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asLong();
                    var a = stack.pop().asLong();
                    stack.push(Value.i64(Long.divideUnsigned(a, b)));
                };
        instructions[OpCode.I32_REM_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asInt();
                    var a = stack.pop().asInt();
                    stack.push(Value.i32(a % b));
                };
        instructions[OpCode.I32_REM_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asUInt();
                    var a = stack.pop().asUInt();
                    stack.push(Value.i32(a % b));
                };
        instructions[OpCode.I64_AND.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asLong();
                    var b = stack.pop().asLong();
                    stack.push(Value.i64(a & b));
                };
        instructions[OpCode.I64_OR.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asLong();
                    var b = stack.pop().asLong();
                    stack.push(Value.i64(a | b));
                };
        instructions[OpCode.I64_XOR.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asLong();
                    var b = stack.pop().asLong();
                    stack.push(Value.i64(a ^ b));
                };
        instructions[OpCode.I64_SHL.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var c = stack.pop().asLong();
                    var v = stack.pop().asLong();
                    stack.push(Value.i64(v << c));
                };
        instructions[OpCode.I64_SHR_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var c = stack.pop().asLong();
                    var v = stack.pop().asLong();
                    stack.push(Value.i64(v >> c));
                };
        instructions[OpCode.I64_SHR_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var c = stack.pop().asLong();
                    var v = stack.pop().asLong();
                    stack.push(Value.i64(v >>> c));
                };
        instructions[OpCode.I64_REM_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asLong();
                    var a = stack.pop().asLong();
                    stack.push(Value.i64(a % b));
                };
        instructions[OpCode.I64_REM_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var b = stack.pop().asLong();
                    var a = stack.pop().asLong();
                    stack.push(Value.i64(Long.remainderUnsigned(a, b)));
                };
        instructions[OpCode.I64_ROTL.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var c = stack.pop().asLong();
                    var v = stack.pop().asLong();
                    var z = (v << c) | (v >>> (64 - c));
                    stack.push(Value.i64(z));
                };
        instructions[OpCode.I64_ROTR.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var c = stack.pop().asLong();
                    var v = stack.pop().asLong();
                    var z = (v >>> c) | (v << (64 - c));
                    stack.push(Value.i64(z));
                };
        instructions[OpCode.I64_CLZ.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop();
                    var count = Long.numberOfLeadingZeros(tos.asLong());
                    stack.push(Value.i64(count));
                };
        instructions[OpCode.I64_CTZ.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop();
                    var count = Long.numberOfTrailingZeros(tos.asLong());
                    stack.push(Value.i64(count));
                };
        instructions[OpCode.I64_POPCNT.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asLong();
                    var count = Long.bitCount(tos);
                    stack.push(Value.i64(count));
                };
        instructions[OpCode.F32_NEG.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asFloat();

                    float result;
                    if (Float.isNaN(tos)) {
                        result = Float.intBitsToFloat(Float.floatToRawIntBits(tos) ^ 0x80000000);
                    } else {
                        result = -1.0f * tos;
                    }

                    stack.push(Value.fromFloat(result));
                };
        instructions[OpCode.F64_NEG.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asDouble();

                    double result;
                    if (Double.isNaN(tos)) {
                        result =
                                Double.longBitsToDouble(
                                        Double.doubleToRawLongBits(tos) ^ 0x8000000000000000L);
                    } else {
                        result = -1.0d * tos;
                    }

                    stack.push(Value.fromDouble(result));
                };
        instructions[OpCode.CALL.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var funcId = (int) operands[0];
                    var typeId = instance.functionType(funcId);
                    var type = instance.type(typeId);
                    // given a list of param types, let's pop those params off the stack
                    // and pass as args to the function call
                    var args = extractArgsForParams(stack, type.params());
                    call(stack, instance, callStack, funcId, args, type, false);
                };
        instructions[OpCode.I32_AND.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asInt();
                    var b = stack.pop().asInt();
                    stack.push(Value.i32(a & b));
                };
        instructions[OpCode.I32_OR.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asInt();
                    var b = stack.pop().asInt();
                    stack.push(Value.i32(a | b));
                };
        instructions[OpCode.I32_XOR.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asInt();
                    var b = stack.pop().asInt();
                    stack.push(Value.i32(a ^ b));
                };
        instructions[OpCode.I32_SHL.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var c = stack.pop().asInt();
                    var v = stack.pop().asInt();
                    stack.push(Value.i32(v << c));
                };
        instructions[OpCode.I32_SHR_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var c = stack.pop().asInt();
                    var v = stack.pop().asInt();
                    stack.push(Value.i32(v >> c));
                    ;
                };
        instructions[OpCode.I32_SHR_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var c = stack.pop().asInt();
                    var v = stack.pop().asInt();
                    stack.push(Value.i32(v >>> c));
                };
        instructions[OpCode.I32_ROTL.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var c = stack.pop().asInt();
                    var v = stack.pop().asInt();
                    var z = (v << c) | (v >>> (32 - c));
                    stack.push(Value.i32(z));
                };
        instructions[OpCode.I32_ROTR.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var c = stack.pop().asInt();
                    var v = stack.pop().asInt();
                    var z = (v >>> c) | (v << (32 - c));
                    stack.push(Value.i32(z));
                };
        instructions[OpCode.F32_ADD.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asFloat();
                    var b = stack.pop().asFloat();
                    stack.push(Value.fromFloat(a + b));
                };
        instructions[OpCode.F64_ADD.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asDouble();
                    var b = stack.pop().asDouble();
                    stack.push(Value.fromDouble(a + b));
                };
        instructions[OpCode.F32_SUB.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asFloat();
                    var b = stack.pop().asFloat();
                    stack.push(Value.fromFloat(b - a));
                };
        instructions[OpCode.F64_SUB.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asDouble();
                    var b = stack.pop().asDouble();
                    stack.push(Value.fromDouble(b - a));
                };
        instructions[OpCode.F32_MUL.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asFloat();
                    var b = stack.pop().asFloat();
                    stack.push(Value.fromFloat(b * a));
                };
        instructions[OpCode.F64_MUL.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asDouble();
                    var b = stack.pop().asDouble();
                    stack.push(Value.fromDouble(b * a));
                };
        instructions[OpCode.F32_DIV.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asFloat();
                    var b = stack.pop().asFloat();
                    stack.push(Value.fromFloat(b / a));
                };
        instructions[OpCode.F64_DIV.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asDouble();
                    var b = stack.pop().asDouble();
                    stack.push(Value.fromDouble(b / a));
                };
        instructions[OpCode.F32_MIN.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asFloat();
                    var b = stack.pop().asFloat();
                    stack.push(Value.fromFloat(Math.min(a, b)));
                };
        instructions[OpCode.F64_MIN.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asDouble();
                    var b = stack.pop().asDouble();
                    stack.push(Value.fromDouble(Math.min(a, b)));
                };
        instructions[OpCode.F32_MAX.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asFloat();
                    var b = stack.pop().asFloat();
                    stack.push(Value.fromFloat(Math.max(a, b)));
                };
        instructions[OpCode.F64_MAX.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asDouble();
                    var b = stack.pop().asDouble();
                    stack.push(Value.fromDouble(Math.max(a, b)));
                };
        instructions[OpCode.F32_SQRT.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var val = stack.pop().asFloat();
                    stack.push(Value.fromFloat((float) Math.sqrt(val)));
                };
        instructions[OpCode.F64_SQRT.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var val = stack.pop().asDouble();
                    stack.push(Value.fromDouble(Math.sqrt(val)));
                };
        instructions[OpCode.F32_FLOOR.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var val = stack.pop().asFloat();
                    stack.push(Value.fromFloat((float) Math.floor(val)));
                };
        instructions[OpCode.F64_FLOOR.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var val = stack.pop().asDouble();
                    stack.push(Value.fromDouble(Math.floor(val)));
                };
        instructions[OpCode.F32_CEIL.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var val = stack.pop().asFloat();
                    stack.push(Value.fromFloat((float) Math.ceil(val)));
                };
        instructions[OpCode.F64_CEIL.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var val = stack.pop().asDouble();
                    stack.push(Value.fromDouble(Math.ceil(val)));
                };
        instructions[OpCode.F32_TRUNC.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var val = stack.pop().asFloat();
                    stack.push(
                            Value.fromFloat(
                                    (float) ((val < 0) ? Math.ceil(val) : Math.floor(val))));
                };
        instructions[OpCode.F64_TRUNC.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var val = stack.pop().asDouble();
                    stack.push(Value.fromDouble((val < 0) ? Math.ceil(val) : Math.floor(val)));
                };
        instructions[OpCode.F32_NEAREST.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var val = stack.pop().asFloat();
                    stack.push(Value.fromFloat((float) Math.rint(val)));
                };
        instructions[OpCode.F64_NEAREST.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var val = stack.pop().asDouble();
                    stack.push(Value.fromDouble(Math.rint(val)));
                };
        // For the extend_* operations, note that java
        // automatically does this when casting from
        // smaller to larger primitives
        instructions[OpCode.I32_EXTEND_8_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asByte();
                    stack.push(Value.i32(tos));
                };
        instructions[OpCode.I32_EXTEND_16_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var original = stack.pop().asInt() & 0xFFFF;
                    if ((original & 0x8000) != 0) original |= 0xFFFF0000;
                    stack.push(Value.i32(original & 0xFFFFFFFFL));
                };
        instructions[OpCode.I64_EXTEND_8_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asByte();
                    stack.push(Value.i64(tos));
                };
        instructions[OpCode.I64_EXTEND_16_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asShort();
                    stack.push(Value.i64(tos));
                };
        instructions[OpCode.I64_EXTEND_32_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asInt();
                    stack.push(Value.i64(tos));
                };
        instructions[OpCode.F64_CONVERT_I64_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asLong();
                    double d;
                    if (tos >= 0) {
                        d = tos;
                    } else {
                        // only preserve 53 bits of precision (plus one for rounding) to
                        // avoid rounding errors (64 - 53 == 11)
                        long sum = tos + 0x3ff;
                        // did the add overflow? add the MSB back on after the shift
                        long shiftIn = ((sum ^ tos) & Long.MIN_VALUE) >>> 10;
                        d = Math.scalb((double) ((sum >>> 11) | shiftIn), 11);
                    }
                    stack.push(Value.f64(Double.doubleToLongBits(d)));
                };
        instructions[OpCode.F64_CONVERT_I32_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    long tos = stack.pop().asUInt();
                    stack.push(Value.f64(Double.doubleToLongBits(tos)));
                };
        instructions[OpCode.F64_CONVERT_I32_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asInt();
                    stack.push(Value.fromDouble(tos));
                };
        instructions[OpCode.F64_PROMOTE_F32.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop();
                    stack.push(Value.fromDouble(tos.asFloat()));
                };
        instructions[OpCode.F64_REINTERPRET_I64.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop();
                    stack.push(Value.f64(tos.asLong()));
                };
        instructions[OpCode.I64_TRUNC_F64_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    double tos = stack.pop().asDouble();

                    if (Double.isNaN(tos)) {
                        throw new WASMRuntimeException("invalid conversion to integer");
                    }

                    long tosL = (long) tos;
                    if (tos == (double) Long.MIN_VALUE) {
                        tosL = Long.MIN_VALUE;
                    } else if (tosL == Long.MIN_VALUE || tosL == Long.MAX_VALUE) {
                        throw new WASMRuntimeException("integer overflow");
                    }

                    stack.push(Value.i64(tosL));
                };
        instructions[OpCode.I32_WRAP_I64.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop();
                    stack.push(Value.i32(tos.asInt()));
                };
        instructions[OpCode.I64_EXTEND_I32_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop();
                    stack.push(Value.i64(tos.asInt()));
                };
        instructions[OpCode.I64_EXTEND_I32_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop();
                    stack.push(Value.i64(tos.asUInt()));
                };
        instructions[OpCode.I32_REINTERPRET_F32.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop();
                    stack.push(Value.i32(tos.asInt()));
                };
        instructions[OpCode.I64_REINTERPRET_F64.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop();
                    stack.push(Value.i64(tos.asLong()));
                };
        instructions[OpCode.F32_REINTERPRET_I32.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop();
                    stack.push(Value.f32(tos.asInt()));
                };
        instructions[OpCode.F32_COPYSIGN.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asFloat();
                    var b = stack.pop().asFloat();

                    if (a == 0xFFC00000L) { // +NaN
                        stack.push(Value.fromFloat(Math.copySign(b, -1)));
                    } else if (a == 0x7FC00000L) { // -NaN
                        stack.push(Value.fromFloat(Math.copySign(b, +1)));
                    } else {
                        stack.push(Value.fromFloat(Math.copySign(b, a)));
                    }
                };
        instructions[OpCode.F32_ABS.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var val = stack.pop().asFloat();
                    stack.push(Value.fromFloat(Math.abs(val)));
                };
        instructions[OpCode.F64_COPYSIGN.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asDouble();
                    var b = stack.pop().asDouble();

                    if (a == 0xFFC0000000000000L) { // +NaN
                        stack.push(Value.fromDouble(Math.copySign(b, -1)));
                    } else if (a == 0x7FC0000000000000L) { // -NaN
                        stack.push(Value.fromDouble(Math.copySign(b, +1)));
                    } else {
                        stack.push(Value.fromDouble(Math.copySign(b, a)));
                    }
                };
        instructions[OpCode.F64_ABS.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var val = stack.pop().asDouble();
                    stack.push(Value.fromDouble(Math.abs(val)));
                };
        instructions[OpCode.F32_NE.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asFloat();
                    var b = stack.pop().asFloat();

                    stack.push(a == b ? Value.FALSE : Value.TRUE);
                };
        instructions[OpCode.F64_NE.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asDouble();
                    var b = stack.pop().asDouble();

                    stack.push(a == b ? Value.FALSE : Value.TRUE);
                };
        instructions[OpCode.F32_LT.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asFloat();
                    var b = stack.pop().asFloat();

                    stack.push(a > b ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.F64_LT.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asDouble();
                    var b = stack.pop().asDouble();

                    stack.push(a > b ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.F32_LE.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asFloat();
                    var b = stack.pop().asFloat();

                    stack.push(a >= b ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.F64_LE.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asDouble();
                    var b = stack.pop().asDouble();

                    stack.push(a >= b ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.F32_GE.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asFloat();
                    var b = stack.pop().asFloat();

                    stack.push(a <= b ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.F64_GE.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asDouble();
                    var b = stack.pop().asDouble();

                    stack.push(a <= b ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.F32_GT.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asFloat();
                    var b = stack.pop().asFloat();

                    stack.push(a < b ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.F64_GT.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var a = stack.pop().asDouble();
                    var b = stack.pop().asDouble();

                    stack.push(a < b ? Value.TRUE : Value.FALSE);
                };
        instructions[OpCode.F32_DEMOTE_F64.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var val = stack.pop().asDouble();
                    stack.push(Value.fromFloat((float) val));
                };
        instructions[OpCode.F32_CONVERT_I32_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asInt();
                    stack.push(Value.fromFloat((float) tos));
                };
        instructions[OpCode.I32_TRUNC_F32_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    float tos = stack.pop().asFloat();

                    if (Float.isNaN(tos)) {
                        throw new WASMRuntimeException("invalid conversion to integer");
                    }

                    if (tos < Integer.MIN_VALUE || tos >= Integer.MAX_VALUE) {
                        throw new WASMRuntimeException("integer overflow");
                    }

                    stack.push(Value.i32((long) tos));
                };
        instructions[OpCode.I32_TRUNC_SAT_F32_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asFloat();

                    if (Float.isNaN(tos)) {
                        tos = 0;
                    } else if (tos < Integer.MIN_VALUE) {
                        tos = Integer.MIN_VALUE;
                    } else if (tos > Integer.MAX_VALUE) {
                        tos = Integer.MAX_VALUE;
                    }

                    stack.push(Value.i32((int) tos));
                };
        instructions[OpCode.I32_TRUNC_SAT_F32_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asFloat();

                    long tosL;
                    if (Float.isNaN(tos) || tos < 0) {
                        tosL = 0L;
                    } else if (tos >= 0xFFFFFFFFL) {
                        tosL = 0xFFFFFFFFL;
                    } else {
                        tosL = (long) tos;
                    }

                    stack.push(Value.i32(tosL));
                };
        instructions[OpCode.I32_TRUNC_SAT_F64_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asDouble();

                    if (Double.isNaN(tos)) {
                        tos = 0;
                    } else if (tos <= Integer.MIN_VALUE) {
                        tos = Integer.MIN_VALUE;
                    } else if (tos >= Integer.MAX_VALUE) {
                        tos = Integer.MAX_VALUE;
                    }

                    stack.push(Value.i32((int) tos));
                };
        instructions[OpCode.I32_TRUNC_SAT_F64_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    double tos = Double.longBitsToDouble(stack.pop().asLong());

                    long tosL;
                    if (Double.isNaN(tos) || tos < 0) {
                        tosL = 0;
                    } else if (tos > 0xFFFFFFFFL) {
                        tosL = 0xFFFFFFFFL;
                    } else {
                        tosL = (long) tos;
                    }
                    stack.push(Value.i32(tosL));
                };
        instructions[OpCode.F32_CONVERT_I32_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asUInt();
                    stack.push(Value.fromFloat((float) tos));
                };
        instructions[OpCode.I32_TRUNC_F32_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asFloat();

                    if (Float.isNaN(tos)) {
                        throw new WASMRuntimeException("invalid conversion to integer");
                    }

                    long tosL = (long) tos;
                    if (tosL < 0 || tosL >= 0xFFFFFFFFL) {
                        throw new WASMRuntimeException("integer overflow");
                    }

                    stack.push(Value.i32(tosL));
                };
        instructions[OpCode.F32_CONVERT_I64_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asLong();
                    stack.push(Value.fromFloat((float) tos));
                };
        instructions[OpCode.F32_CONVERT_I64_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asLong();

                    float f;
                    if (tos >= 0) {
                        f = tos;
                    } else {
                        // only preserve 24 bits of precision (plus one for rounding) to
                        // avoid rounding errors (64 - 24 == 40)
                        long sum = tos + 0xff_ffff_ffffL;
                        // did the add overflow? add the MSB back on after the shift
                        long shiftIn = ((sum ^ tos) & Long.MIN_VALUE) >>> 39;
                        f = Math.scalb((float) ((sum >>> 40) | shiftIn), 40);
                    }

                    stack.push(Value.f32(Float.floatToIntBits(f)));
                };
        instructions[OpCode.F64_CONVERT_I64_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asLong();
                    stack.push(Value.fromDouble((double) tos));
                };
        instructions[OpCode.I64_TRUNC_F32_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asFloat();

                    if (Float.isNaN(tos)) {
                        throw new WASMRuntimeException("invalid conversion to integer");
                    }

                    if (tos >= 2 * (float) Long.MAX_VALUE) {
                        throw new WASMRuntimeException("integer overflow");
                    }

                    long tosL;
                    if (tos < Long.MAX_VALUE) {
                        tosL = (long) tos;
                        if (tosL < 0) {
                            throw new WASMRuntimeException("integer overflow");
                        }
                    } else {
                        // This works for getting the unsigned value because binary addition
                        // yields the correct interpretation in both unsigned &
                        // 2's-complement
                        // no matter which the operands are considered to be.
                        tosL = Long.MAX_VALUE + (long) (tos - (float) Long.MAX_VALUE) + 1;
                        if (tosL >= 0) {
                            // Java's comparison operators assume signed integers. In the
                            // case
                            // that we're in the range of unsigned values where the sign bit
                            // is set, Java considers these values to be negative so we have
                            // to check for >= 0 to detect overflow.
                            throw new WASMRuntimeException("integer overflow");
                        }
                    }

                    stack.push(Value.i64(tosL));
                };
        instructions[OpCode.I64_TRUNC_F64_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asDouble();

                    if (Double.isNaN(tos)) {
                        throw new WASMRuntimeException("invalid conversion to integer");
                    }

                    if (tos >= 2 * (double) Long.MAX_VALUE) {
                        throw new WASMRuntimeException("integer overflow");
                    }

                    long tosL;
                    if (tos < Long.MAX_VALUE) {
                        tosL = (long) tos;
                        if (tosL < 0) {
                            throw new WASMRuntimeException("integer overflow");
                        }
                    } else {
                        // See I64_TRUNC_F32_U for notes on implementation. This is
                        // the double-based equivalent of that.
                        tosL = Long.MAX_VALUE + (long) (tos - (double) Long.MAX_VALUE) + 1;
                        if (tosL >= 0) {
                            throw new WASMRuntimeException("integer overflow");
                        }
                    }

                    stack.push(Value.i64(tosL));
                };
        instructions[OpCode.I64_TRUNC_SAT_F32_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asFloat();

                    if (Float.isNaN(tos)) {
                        tos = 0;
                    } else if (tos <= Long.MIN_VALUE) {
                        tos = Long.MIN_VALUE;
                    } else if (tos >= Long.MAX_VALUE) {
                        tos = Long.MAX_VALUE;
                    }

                    stack.push(Value.i64((long) tos));
                };
        instructions[OpCode.I64_TRUNC_SAT_F32_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asFloat();

                    long tosL;
                    if (Float.isNaN(tos) || tos < 0) {
                        tosL = 0L;
                    } else if (tos > Math.pow(2, 64) - 1) {
                        tosL = 0xFFFFFFFFFFFFFFFFL;
                    } else {
                        if (tos < Long.MAX_VALUE) {
                            tosL = (long) tos;
                        } else {
                            // See I64_TRUNC_F32_U for notes on implementation. This is
                            // the double-based equivalent of that.
                            tosL = Long.MAX_VALUE + (long) (tos - (double) Long.MAX_VALUE) + 1;
                            if (tosL >= 0) {
                                throw new WASMRuntimeException("integer overflow");
                            }
                        }
                    }

                    stack.push(Value.i64(tosL));
                };
        instructions[OpCode.I64_TRUNC_SAT_F64_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asDouble();

                    if (Double.isNaN(tos)) {
                        tos = 0;
                    } else if (tos <= Long.MIN_VALUE) {
                        tos = Long.MIN_VALUE;
                    } else if (tos >= Long.MAX_VALUE) {
                        tos = Long.MAX_VALUE;
                    }

                    stack.push(Value.i64((long) tos));
                };
        instructions[OpCode.I64_TRUNC_SAT_F64_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    double tos = stack.pop().asDouble();

                    long tosL;
                    if (Double.isNaN(tos) || tos < 0) {
                        tosL = 0L;
                    } else if (tos > Math.pow(2, 64) - 1) {
                        tosL = 0xFFFFFFFFFFFFFFFFL;
                    } else {
                        if (tos < Long.MAX_VALUE) {
                            tosL = (long) tos;
                        } else {
                            // See I64_TRUNC_F32_U for notes on implementation. This is
                            // the double-based equivalent of that.
                            tosL = Long.MAX_VALUE + (long) (tos - (double) Long.MAX_VALUE) + 1;
                            if (tosL >= 0) {
                                throw new WASMRuntimeException("integer overflow");
                            }
                        }
                    }

                    stack.push(Value.i64(tosL));
                };
        instructions[OpCode.I32_TRUNC_F64_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asDouble();

                    if (Double.isNaN(tos)) {
                        throw new WASMRuntimeException("invalid conversion to integer");
                    }

                    var tosL = (long) tos;
                    if (tosL < Integer.MIN_VALUE || tosL > Integer.MAX_VALUE) {
                        throw new WASMRuntimeException("integer overflow");
                    }

                    stack.push(Value.i32(tosL));
                };
        instructions[OpCode.I32_TRUNC_F64_U.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    double tos = stack.pop().asDouble();
                    if (Double.isNaN(tos)) {
                        throw new WASMRuntimeException("invalid conversion to integer");
                    }

                    var tosL = (long) tos;
                    if (tosL < 0 || tosL > 0xFFFFFFFFL) {
                        throw new WASMRuntimeException("integer overflow");
                    }
                    stack.push(Value.i32(tosL & 0xFFFFFFFFL));
                };
        instructions[OpCode.I64_TRUNC_F32_S.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tos = stack.pop().asFloat();

                    if (Float.isNaN(tos)) {
                        throw new WASMRuntimeException("invalid conversion to integer");
                    }

                    if (tos < Long.MIN_VALUE || tos >= Long.MAX_VALUE) {
                        throw new WASMRuntimeException("integer overflow");
                    }

                    stack.push(Value.i64((long) tos));
                };
        instructions[OpCode.MEMORY_INIT.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var segmentId = (int) operands[0];
                    var memidx = (int) operands[1];
                    if (memidx != 0)
                        throw new WASMRuntimeException(
                                "We don't support non zero index for memory: " + memidx);
                    var size = stack.pop().asInt();
                    var offset = stack.pop().asInt();
                    var destination = stack.pop().asInt();
                    instance.memory().initPassiveSegment(segmentId, destination, offset, size);
                };
        instructions[OpCode.TABLE_INIT.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tableidx = (int) operands[1];
                    var elementidx = (int) operands[0];

                    var size = stack.pop().asInt();
                    var elemidx = stack.pop().asInt();
                    var offset = stack.pop().asInt();
                    var end = offset + size;

                    var table = instance.table(tableidx);
                    if (table == null) {
                        table = instance.imports().table(tableidx).table();
                    }

                    if (size < 0
                            || elementidx > instance.elementCount()
                            || instance.element(elementidx) == null
                            || elemidx + size > instance.element(elementidx).size()
                            || end > table.size()) {
                        throw new WASMRuntimeException("out of bounds table access");
                    }

                    for (int i = offset; i < end; i++) {
                        var val = getRuntimeElementValue(instance, elementidx, elemidx++);
                        if (val > instance.functionCount()) {
                            throw new WASMRuntimeException("out of bounds table access");
                        }
                        table.setRef(i, val);
                    }
                };
        instructions[OpCode.DATA_DROP.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var segment = (int) operands[0];
                    instance.memory().drop(segment);
                };
        instructions[OpCode.MEMORY_COPY.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var memidxSrc = (int) operands[0];
                    var memidxDst = (int) operands[1];
                    if (memidxDst != 0 && memidxSrc != 0)
                        throw new WASMRuntimeException(
                                "We don't support non zero index for memory: "
                                        + memidxSrc
                                        + " "
                                        + memidxDst);
                    var size = stack.pop().asInt();
                    var offset = stack.pop().asInt();
                    var destination = stack.pop().asInt();
                    instance.memory().copy(destination, offset, size);
                };
        instructions[OpCode.TABLE_COPY.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tableidxSrc = (int) operands[1];
                    var tableidxDst = (int) operands[0];

                    var size = stack.pop().asInt();
                    var s = stack.pop().asInt();
                    var d = stack.pop().asInt();
                    var src = instance.table(tableidxSrc);
                    var dest = instance.table(tableidxDst);

                    if (size < 0
                            || (s < 0 || (size + s) > src.size())
                            || (d < 0 || (size + d) > dest.size())) {
                        throw new WASMRuntimeException("out of bounds table access");
                    }

                    for (int i = size - 1; i >= 0; i--) {
                        if (d <= s) {
                            var val = src.ref(s++);
                            dest.setRef(d++, val.asFuncRef());
                        } else {
                            var val = src.ref(s + i);
                            dest.setRef(d + i, val.asFuncRef());
                        }
                    }
                };
        instructions[OpCode.TABLE_FILL.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tableidx = (int) operands[0];

                    var size = stack.pop().asInt();
                    var val = stack.pop().asExtRef();
                    var offset = stack.pop().asInt();
                    var end = offset + size;

                    var table = instance.table(tableidx);
                    if (table == null) {
                        table = instance.imports().table(tableidx).table();
                    }

                    if (size < 0 || end > table.size()) {
                        throw new WASMRuntimeException("out of bounds table access");
                    }

                    for (int i = offset; i < end; i++) {
                        table.setRef(i, val);
                    }
                };
        instructions[OpCode.TABLE_SIZE.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tableidx = (int) operands[0];
                    var table = instance.table(tableidx);
                    if (table == null) {
                        table = instance.imports().table(tableidx).table();
                    }

                    stack.push(Value.i32(table.size()));
                };
        instructions[OpCode.TABLE_GROW.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var tableidx = (int) operands[0];
                    var table = instance.table(tableidx);
                    if (table == null) {
                        table = instance.imports().table(tableidx).table();
                    }

                    var size = stack.pop().asInt();
                    var valValue = stack.pop();
                    var val = valValue.asExtRef();

                    var res = table.grow(size, val);
                    stack.push(Value.i32(res));
                };
        instructions[OpCode.REF_FUNC.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    stack.push(Value.funcRef(operands[0]));
                };
        instructions[OpCode.REF_NULL.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var type = ValueType.byId(operands[0]);
                    stack.push(new Value(type, (long) REF_NULL_VALUE));
                };
        instructions[OpCode.REF_IS_NULL.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var val = stack.pop();
                    stack.push(
                            val.equals(Value.EXTREF_NULL) || val.equals(Value.FUNCREF_NULL)
                                    ? Value.TRUE
                                    : Value.FALSE);
                };
        instructions[OpCode.ELEM_DROP.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    var x = (int) operands[0];
                    instance.setElement(x, null);
                };
        instructions[OpCode.RETURN.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    frame.shouldReturn = true;
                };
        instructions[OpCode.END.ordinal()] =
                (frame, stack, instance, callStack, instruction, operands) -> {
                    if (frame.doControlTransfer && frame.isControlFrame) {
                        doControlTransfer(instance, stack, frame, instruction.scope());
                    } else {
                        frame.endOfNonControlBlock();
                    }

                    // if this is the last end, then we're done with
                    // the function
                    if (frame.isLastBlock()) {
                        frame.shouldReturn = true;
                    }
                };
    }
    ;

    static void eval(MStack stack, Instance instance, ArrayDeque<StackFrame> callStack)
            throws ChicoryException {

        try {
            var frame = callStack.peek();

            while (!frame.terminated()) {
                if (frame.shouldReturn) return;
                var instruction = frame.loadCurrentInstruction();
                //                LOGGER.log(
                //                        System.Logger.Level.DEBUG,
                //                        "func="
                //                                + frame.funcId
                //                                + "@"
                //                                + frame.pc
                //                                + ": "
                //                                + instruction
                //                                + " stack="
                //                                + stack);
                var opcode = instruction.opcode();
                var operands = instruction.operands();
                var exec = instructions[opcode.ordinal()];
                exec.execute(frame, stack, instance, callStack, instruction, operands);
            }
        } catch (ChicoryException e) {
            // propagate ChicoryExceptions
            throw e;
        } catch (ArithmeticException e) {
            if (e.getMessage().equalsIgnoreCase("/ by zero")
                    || e.getMessage()
                            .contains("divide by zero")) { // On Linux i64 throws "BigInteger divide
                // by zero"
                throw new WASMRuntimeException("integer divide by zero: " + e.getMessage(), e);
            }
            throw new WASMRuntimeException(e.getMessage(), e);
        } catch (IndexOutOfBoundsException e) {
            throw new WASMRuntimeException("undefined element " + e.getMessage(), e);
        } catch (Exception e) {
            throw new WASMRuntimeException("An underlying Java exception occurred", e);
        }
    }

    private static int numberOfValuesToReturn(Instance instance, Instruction scope) {
        if (scope.opcode() == OpCode.END) {
            return 0;
        }
        var typeId = (int) scope.operands()[0];
        if (typeId == 0x40) { // epsilon
            return 0;
        }
        if (ValueType.byId(typeId) != null) {
            return 1;
        }
        return instance.type(typeId).returns().length;
    }

    private static Value prepareControlTransfer(StackFrame frame, MStack stack, boolean consume) {
        frame.doControlTransfer = true;

        var unwindStack = stack.unwindFrame();
        stack.resetUnwindFrame();
        Value predValue = null;
        if (consume) {
            predValue = stack.pop();
        }
        if (unwindStack == null) {
            stack.setUnwindFrame(new ArrayDeque<>());
        } else {
            stack.setUnwindFrame(unwindStack);
        }

        return predValue;
    }

    private static void doControlTransfer(
            Instance instance, MStack stack, StackFrame frame, Instruction scope) {
        // reset the control transfer
        frame.doControlTransfer = false;
        var unwindStack = stack.unwindFrame();
        stack.resetUnwindFrame();

        Value[] returns = new Value[numberOfValuesToReturn(instance, scope)];
        for (int i = 0; i < returns.length; i++) {
            if (stack.size() > 0) returns[i] = stack.pop();
        }

        // drop everything till the previous label
        frame.dropValuesOutOfBlock(stack);

        if (frame.isLastBlock()) {
            while (!unwindStack.isEmpty()) {
                stack.push(unwindStack.pop());
            }
        }

        for (int i = 0; i < returns.length; i++) {
            Value value = returns[returns.length - 1 - i];
            if (value != null) {
                stack.push(value);
            }
        }
    }

    private static int getRuntimeElementValue(Instance instance, int idx, int s) {
        var elem = instance.element(idx);
        var type = elem.elemType();
        int val;
        switch (type) {
            case Type:
                {
                    var t = (ElemType) elem;
                    val = computeConstantValue(t.exprInstructions());
                    break;
                }
            case Elem:
                {
                    var e = (ElemElem) elem;
                    var expr = e.exprs()[s];
                    val = computeConstantValue(expr);
                    break;
                }
            case Func:
                {
                    var f = (ElemFunc) elem;
                    val = (int) f.funcIndices()[s];
                    break;
                }
            default:
                {
                    throw new WASMRuntimeException("Element Type not recognized " + type);
                }
        }
        return val;
    }

    List<StackFrame> getStackTrace() {
        return List.copyOf(callStack);
    }

    static Value[] extractArgsForParams(MStack stack, ValueType[] params) {
        if (params == null) {
            return Value.EMPTY_VALUES;
        }
        var args = new Value[params.length];
        for (var i = params.length; i > 0; i--) {
            var p = stack.pop();
            var t = params[i - 1];
            if (p.type() != t) {
                throw new RuntimeException("Type error when extracting args.");
            }
            args[i - 1] = p;
        }
        return args;
    }

    protected static void verifyIndirectCall(FunctionType actual, FunctionType expected)
            throws ChicoryException {
        if (!actual.typesMatch(expected)) {
            throw new ChicoryException("indirect call type mismatch");
        }
    }
}
