import random
import sys

import jpamb
import jvm
import jvm.state as jvmc


def binary(op, v1: int, v2: int) -> int | str:
    match op:
        case jvm.BinaryOpr.Div:
            try:
                return v1 // v2
            except ZeroDivisionError:
                return "divide by zero"
        case jvm.BinaryOpr.Add:
            return v1 + v2
        case jvm.BinaryOpr.Sub:
            return v1 - v2
        case jvm.BinaryOpr.Mul:
            return v1 * v2
        case jvm.BinaryOpr.Rem:
            try:
                return v1 % v2
            except ZeroDivisionError:
                return "divide by zero"
        case a:
            raise NotImplementedError(f"Unhandled binary {op!r}")


def compare(op, v1: int, v2: int) -> bool:
    match op:
        case jvm.CmpOpr.Eq:
            return v1 == v2
        case jvm.CmpOpr.Ne:
            return v1 != v2
        case jvm.CmpOpr.Lt:
            return v1 < v2
        case jvm.CmpOpr.Le:
            return v1 <= v2
        case jvm.CmpOpr.Gt:
            return v1 > v2
        case jvm.CmpOpr.Ge:
            return v1 >= v2
        case _:
            raise NotImplementedError(f"Unhandled comparation {op!r}")

def truncate(value: int, bits: int, signed: bool) -> int:
    mask = (1 << bits) - 1
    value &= mask
    if signed and value >= (1 << (bits - 1)):
        value -= 1 << bits
    return value


def step(bc: jpamb.Bytecode, state: jvmc.State) -> tuple[jvmc.PC, jvmc.State | str]:
    assert isinstance(state, jvmc.State), f"expected state but got {state}"
    frame = state.frames.peek()
    pc = frame.pc
    opr = bc[pc]
    output = state
    print(f"Stepping {pc}:\n > {opr}", file=sys.stderr)
    match opr:
        case jvm.Push(type=t, value=v):
            match t:
                case jvm.Int():
                    frame.stack.push(jvmc.StackInt(v))
                case jvm.Boolean():
                    frame.stack.push(jvmc.StackInt(1 if v else 0))
                case jvm.Char():
                    frame.stack.push(jvmc.StackInt(ord(v)))
                case jvm.Reference():
                    frame.stack.push(jvmc.StackReference(v))
                case _:
                    ref = state.heap.new(jvmc.HeapString(v))
                    frame.stack.push(ref)
            frame.pc += 1

        case jvm.Binary(type=jvm.Int(), operant=op):
            v2, v1 = frame.stack.pop(), frame.stack.pop()
            assert isinstance(v1, jvmc.StackInt), f"expected int, but got {v1}"
            assert isinstance(v2, jvmc.StackInt), f"expected int, but got {v2}"

            value = binary(op, v1.value, v2.value)

            if isinstance(value, str):
                output = value
            else:
                frame.stack.push(jvmc.StackInt(value))
                frame.pc += 1

        case jvm.Return(type=t):
            if t is None:
                v1 = jvmc.StackInt(0)
            else:
                v1 = frame.stack.pop()
            assert isinstance(v1, jvmc.StackInt), f"expected int, but got {v1}"

            state.frames.pop()
            if state.frames:
                frame = state.frames.peek()
                frame.stack.push(v1)
                frame.pc += 1
            else:
                output = "ok"

        case jvm.Store(type=jvm.Reference(), index=n):
            v = frame.stack.pop()
            assert isinstance(v, jvmc.StackReference), f"expected reference, but got {v}"
            frame.locals[n] = v
            frame.pc += 1

        case jvm.Store(type=jvm.Int(), index=n):
            v = frame.stack.pop()
            assert isinstance(v, jvmc.StackInt), f"expected int, but got {v}"
            frame.locals[n] = v
            frame.pc += 1

        case jvm.ArrayStore(type=jvm.Int()):
            value, index, ref = frame.stack.pop(), frame.stack.pop(), frame.stack.pop()
            assert isinstance(value, jvmc.StackInt), f"expected int, but got {value}"
            assert isinstance(index, jvmc.StackInt), f"expected int, but got {index}"
            assert isinstance(ref, jvmc.StackReference), f"expected reference, but got {ref}"

            if ref.value == 0:
                output = "null pointer"
            else:
                array = state.heap[ref]
                assert isinstance(array, jvmc.HeapArray), f"expected array, but got {array}"
                if 0 <= index.value < len(array.values):
                    array.values[index.value] = value.value
                    frame.pc += 1
                else:
                    output = "out of bounds"

        case jvm.ArrayLength():
            ref = frame.stack.pop()
            assert isinstance(ref, jvmc.StackReference), f"expected reference, but got {ref}"
            if ref.value == 0:
                output = "null pointer"
            else:
                array = state.heap[ref]
                assert isinstance(array, jvmc.HeapArray), f"expected array, but got {array}"
                frame.stack.push(jvmc.StackInt(len(array.values)))
                frame.pc += 1

        case jvm.Dup():
            v = frame.stack.pop()
            frame.stack.push(v)
            frame.stack.push(v)
            frame.pc += 1

        case jvm.Incr(index=n, amount=v):
            local = frame.locals[n]
            assert isinstance(local, jvmc.StackInt), f"expected int, but got {local}"
            frame.locals[n] = jvmc.StackInt(local.value + v)
            frame.pc += 1

        case jvm.Goto(target=target):
            frame.pc %= target

        case jvm.InvokeStatic(method=methodid):
            callee = bc.getmethod(methodid)
            new_frame = jvmc.Frame.from_method(callee)
            nparams = len(methodid.extension.params)
            args = [frame.stack.pop() for _ in range(nparams)]
            for i, v in enumerate(reversed(args)):
                new_frame.locals[i] = v
            state.frames.push(new_frame)

        case jvm.InvokeVirtual(method=methodid):
            cn = methodid.classname
            name = methodid.extension.name

            if cn == jvm.ClassName("java.lang.String") and name == "equals":
                other_ref = frame.stack.pop()
                this_ref = frame.stack.pop()
                assert isinstance(this_ref, jvmc.StackReference), f"expected reference, but got {this_ref}"
                this_str = state.heap[this_ref]
                assert isinstance(this_str, jvmc.HeapString), f"expected string, but got {this_str}"

                if isinstance(other_ref, jvmc.StackReference) and other_ref.value != 0:
                    other = state.heap[other_ref]
                    result = isinstance(other, jvmc.HeapString) and other.content == this_str.content
                else:
                    result = False

                frame.stack.push(jvmc.StackInt(1 if result else 0))
                frame.pc += 1

            else:
                callee = bc.getmethod(methodid)
                new_frame = jvmc.Frame.from_method(callee)
                nparams = len(methodid.extension.params)
                args = [frame.stack.pop() for _ in range(nparams)]
                ref = frame.stack.pop()
                assert isinstance(ref, jvmc.StackReference), f"expected reference, but got {ref}"

                if ref.value == 0:
                    output = "null pointer"
                else:
                    obj = state.heap[ref]
                    assert isinstance(obj, jvmc.HeapObject), f"expected object, but got {obj}"
                    if obj.classname != methodid.extension.classname:
                        output = "class cast"
                    else:
                        new_frame.locals[0] = ref
                        for i, v in enumerate(reversed(args)):
                            new_frame.locals[i + 1] = v
                        state.frames.push(new_frame)

        case jvm.Cast(from_=jvm.Int(), to_=t):
            v = frame.stack.pop()
            assert isinstance(v, jvmc.StackInt), f"expected int, but got {v}"
            match t:
                case jvm.Short():
                    value = truncate(v.value, 16, signed=True)
                case jvm.Byte():
                    value = truncate(v.value, 8, signed=True)
                case jvm.Char():
                    value = truncate(v.value, 16, signed=False)
                case a:
                    raise NotImplementedError(f"Unhandled cast target {a!r}")
            frame.stack.push(jvmc.StackInt(value))
            frame.pc += 1

        case jvm.Cast(from_=jvm.Reference(), to_=t):
            v = frame.stack.pop()
            assert isinstance(v, jvmc.StackReference), f"expected reference, but got {v}"
            if v.value == 0:
                frame.stack.push(v)
                frame.pc += 1
            else:
                obj = state.heap[v]
                assert isinstance(obj, jvmc.HeapObject), f"expected object, but got {obj}"
                if obj.classname == t.extension.name:
                    frame.stack.push(v)
                    frame.pc += 1
                else:
                    output = "class cast"


        case jvm.Get(static=True, field=field):
            # Hack - Only handle the assertion case
            assert field.extension.name == "$assertionsDisabled"

            # Hack - Assuming assertions are never disabled
            frame.stack.push(jvmc.StackInt(0))
            frame.pc += 1

        case jvm.Ifz(condition=op, target=target):
            value = frame.stack.pop()
            assert isinstance(value, jvmc.StackInt), f"expected int, but got {value}"

            if compare(op, value.value, 0):
                frame.pc %= target
            else:
                frame.pc += 1

        case jvm.If(condition=op, target=target):
            v2, v1 = frame.stack.pop(), frame.stack.pop()
            assert isinstance(v1, jvmc.StackInt), f"expected int, but got {v1}"
            assert isinstance(v2, jvmc.StackInt), f"expected int, but got {v2}"
            if compare(op, v1.value, v2.value):
                frame.pc %= target
            else:
                frame.pc += 1

        case jvm.Load(type=t, index=n):
            v = frame.locals[n]
            assert v is not None, f"loading uninitialized local {n}"
            frame.stack.push(v)
            frame.pc += 1

        case jvm.ArrayLoad(type=t):
            index, ref = frame.stack.pop(), frame.stack.pop()
            assert isinstance(index, jvmc.StackInt), f"expected int, but got {index}"
            assert isinstance(ref, jvmc.StackReference), f"expected reference, but got {ref}"

            if ref.value == 0:
                output = "null pointer"
            else:
                array = state.heap[ref]
                assert isinstance(array, jvmc.HeapArray), f"expected array, but got {array}"
                if 0 <= index.value < len(array.values):
                    frame.stack.push(jvmc.StackInt(array.values[index.value]))
                    frame.pc += 1
                else:
                    output = "out of bounds"

        case jvm.NewArray(type=jvm.Int(), offset=offset, dim=dim):
            size = frame.stack.pop()
            # assert isinstance(size, jvmc.StackInt), f"expected int, but got {size}"
            array = jvmc.HeapArray(jvm.Int(), [0] * size.value)
            ref = state.heap.new(array)
            frame.stack.push(ref)
            frame.pc += 1

        case jvm.New(classname=jvm.ClassName("java.lang.AssertionError")):
            # Hack -- if we create an assertion error, we probably also throw it.
            output = "assertion error"

        case a:
            raise NotImplementedError(a.help())

    assert isinstance(output, (jvmc.State, str))

    return pc, output


def initial(bc: jpamb.Bytecode, methodid: jvm.AbsMethodID, input: jpamb.Input):
    frame = jvmc.Frame.from_method(bc.getmethod(methodid))
    state = jvmc.State(jvmc.Heap(), jvmc.CallStack.from_frames([frame]))
    for i, v in enumerate(input.values):
        # Convert arbitrary values into local values
        match v:
            case jpamb.case.Boolean(value):
                frame.locals[i] = jvmc.StackInt(1 if value else 0)
            case jpamb.case.Int(value):
                frame.locals[i] = jvmc.StackInt(value)
            case jpamb.case.Array(contains=type, values=values):
                match type:
                    case jvm.Char():
                        ref = state.heap.new(
                            jvmc.HeapArray(type, [ord(a) for a in values])
                        )
                    case jvm.Int():
                        ref = state.heap.new(jvmc.HeapArray(type, [a for a in values]))
                frame.locals[i] = ref
            case jpamb.case.String(value=value):
                ref = state.heap.new(jvmc.HeapString(value))
                frame.locals[i] = ref
            case a:
                raise NotImplementedError(
                    f"Do not know how to convert values of type {a!r} to a local value"
                )

    return state


def interpret():
    """The entry point for the interpreter"""

    methodid, input, max_steps = jpamb.getcase(
        "dynamic",
        "1.0",
        "Cooked-Pikachu",
        ["dynamic", "python"],
        for_science=True,
    )

    suite, eff = jpamb.setup()
    bc = jpamb.Bytecode(suite, eff, {})

    state = initial(bc, methodid, input)

    last = jpamb.emit_init(state)

    for x in range(max_steps):
        pc, state = step(bc, state)
        last = jpamb.emit_step(last, pc, state)

        if isinstance(state, str):
            break


def fuzz_input(rand: random.Random, methodid: jvm.AbsMethodID) -> jpamb.case.Input:
    input = []
    # 1. come up with possible inputs
    for p in methodid.extension.params:
        match p:
            case jvm.Int():
                input.append(jpamb.case.Int(rand.randint(-(1 << 31), 1 << 31)))
            case jvm.Boolean():
                input.append(jpamb.case.Boolean(1 == rand.randint(0, 1)))
            case a:
                raise NotImplementedError(
                    "Don't know how to create random values for {input}"
                )

    return jpamb.case.Input(input)


def analyse():
    """The dynamic analysis, e.g. in this case a (dumb) fuzzer."""

    methodid = jpamb.getmethodid(
        "dynamic",
        "1.0",
        "Cooked-Pikachu",
        ["dynamic", "python"],
        for_science=True,
    )

    suite, eff = jpamb.setup()
    bc = jpamb.Bytecode(suite, eff, {})

    MAX_STEPS = 200

    import random

    # Make the randomness deterministic
    rand = random.Random(0)

    behaviors = set()
    # Try 10 random inputs
    for i in range(10):
        input = fuzz_input(rand, methodid)
        state = initial(bc, methodid, input)

        for x in range(MAX_STEPS):
            _, state = step(bc, state)
            if isinstance(state, str):
                behaviors.add(state)
                break

    for query in jpamb.QUERIES:
        if query in behaviors:
            if query == "*":
                print(f"{query};timeout")
            else:
                print(f"{query};found")
        if len(input.inputs) == 0:
            print(f"{query};no")
        else:
            print(f"{query};not-found")
