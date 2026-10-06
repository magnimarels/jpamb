import heapq
import itertools
import sys
from collections.abc import Iterable
from dataclasses import dataclass, field

from abstractions import SignSet

import jpamb
import sexpr
from jpamb import jvm
from jvm.state import PC, StackInt


@dataclass(frozen=True)
class State(sexpr.AsSExpr):
    locals: tuple[SignSet, ...]
    stack: tuple[SignSet, ...]

    def __post_init__(self):
        assert isinstance(self.locals, tuple)
        assert isinstance(self.stack, tuple)

    def __str__(self):
        return f"{', '.join(map(str, self.locals))}/{':'.join(map(str, self.stack))}"

    def __or__(self, other):
        assert isinstance(other, State), f"Expected State but got {other!r}"
        assert len(self.stack) == len(other.stack), "Stacks should be equal lenght"
        assert len(self.locals) == len(other.locals), "Locals should be equal lenght"

        return State(
            tuple(s1 | s2 for s1, s2 in zip(self.locals, other.locals)),
            tuple(s1 | s2 for s1, s2 in zip(self.stack, other.stack)),
        )

    def push(self, value: SignSet):
        assert isinstance(value, SignSet), f"Expected sign set but got {value}"
        return State(self.locals, self.stack + (value,))

    def pop(self, number=1):
        return self.stack[-number:], State(self.locals, self.stack[:-number])

    def load(self, index):
        return self.locals[index]

    def store(self, index, value):
        return State(
            tuple(self.locals[:index]) + (value,) + tuple(self.locals[index + 1 :]),
            self.stack,
        )


def manystep(
    bc: jpamb.Bytecode,
    pc: PC,
    state: State,
) -> Iterable[tuple[PC, object] | str]:
    opr = bc[pc]
    match opr:
        case jvm.Get(static=True, field=field):
            # Hack - Only handle the assertion case
            assert field.extension.name == "$assertionsDisabled"

            # Hack - Assuming assertions are never disabled
            va = SignSet.abstract([StackInt(0)])

            yield (pc + 1, state.push(va))

        case jvm.Ifz(condition=op, target=target):
            [val], after = state.pop(1)

            for res in SignSet.compare(val, SignSet.abstract([StackInt(0)]), op):
                match res:
                    case True:
                        yield (pc % target, after)
                    case False:
                        yield (pc + 1, after)
                    case err:
                        yield err

        case jvm.Load(index=i):
            va = state.load(i)
            yield (pc + 1, state.push(va))

        case jvm.Goto(target=t):
            yield (pc % t, state)

        case jvm.Binary(operant=op):
            [v1, v2], after = state.pop(2)
            result, errs = SignSet.arithmetic(v1, v2, op)

            for err in errs:
                yield err

            if result.signs:
                yield (pc + 1, after.push(result))


        case jvm.New(classname=jvm.ClassName("java.lang.AssertionError")):
            # Hack -- if we create an assertion error, we probably also throw it.
            yield "assertion error"

        case jvm.Push(value=None):
            # References are sign sets too: {0} is null, {+} is non-null.
            yield (pc + 1, state.push(SignSet.from_sign("0")))

        case jvm.Push(value=str()):
            # A string constant is a non-null reference.
            yield (pc + 1, state.push(SignSet.from_sign("+")))

        case jvm.Push(value=v):
            va = SignSet.abstract([StackInt(v)])
            yield (pc + 1, state.push(va))

        case jvm.InvokeVirtual(method=m) if m.classname == jvm.ClassName(
            "java.lang.String"
        ):
            # We don't track string contents, so only model the methods we
            # know are pure and only fail on a null receiver.
            name = m.extension.name
            nargs = len(m.extension.params)
            [receiver, *_], after = state.pop(nargs + 1)

            if 0 in receiver.signs:
                yield "null pointer"
            if receiver.signs - {0}:
                match name:
                    case "equals":
                        yield (pc + 1, after.push(SignSet.from_sign("0+")))
                    case "length":
                        yield (pc + 1, after.push(SignSet.from_sign("0+")))
                    case _:
                        raise NotImplementedError(f"String.{name} not supported")

        case jvm.NewArray(type=t, dim=dim):
            if dim != 1:
                raise NotImplementedError(f"NewArray with dim={dim} not supported")

            [count], after = state.pop(1)
            if -1 in count.signs:
                yield "negative array size"
            if count.signs - {-1}:
                yield (pc + 1, after.push(SignSet.from_sign("+")))

        case jvm.Dup():
            [top], after = state.pop(1)
            yield (pc + 1, after.push(top).push(top))


        case jvm.Store(index=i):
            [value], after = state.pop(1)
            yield (pc + 1, after.store(i, value))

        case jvm.ArrayStore(type=t):
            [arr, index, value], after = state.pop(3)
            non_null_arr = arr.signs - {0}

            if 0 in arr.signs:
                yield "null pointer"

            if non_null_arr:
                if -1 in index.signs:
                    yield "out of bounds"
                if index.signs - {-1}:
                    yield "out of bounds"
                    yield (pc + 1, after)

        case jvm.ArrayLength():
            [arr], after = state.pop(1)
            if 0 in arr.signs:
                yield "null pointer"
            if arr.signs - {0}:
                yield (pc + 1, after.push(SignSet.from_sign("0+")))

        case jvm.ArrayLoad(type=t):
            [arr, index], after = state.pop(2)
            non_null_arr = arr.signs - {0}

            if 0 in arr.signs:
                yield "null pointer"

            if non_null_arr:
                if -1 in index.signs:
                    yield "out of bounds"
                if index.signs - {-1}:
                    yield "out of bounds"
                    yield (pc + 1, after.push(SignSet.top()))

        case jvm.If(condition=op, target=target):
            [v1, v2], after = state.pop(2)
            for res in SignSet.compare(v1, v2, op):
                match res:
                    case True:
                        yield (pc % target, after)
                    case False:
                        yield (pc + 1, after)
                    case err:
                        yield err

        case jvm.Incr(index=i, amount=amount):
            va = state.load(i)
            result, errs = SignSet.arithmetic(va, SignSet.abstract([StackInt(amount)]), jvm.BinaryOpr.Add)

            for err in errs:
                yield err

            if result.signs:
                yield (pc + 1, state.store(i, result))

                

        case jvm.Cast(from_=jvm.Int(), to_=to):
            [val], after = state.pop(1)
            match to:
                case jvm.Short() | jvm.Byte():
                    # Truncation can flip the sign or hit zero (e.g. 65536 -> 0)
                    result = val if val.signs <= {0} else SignSet.top()
                case jvm.Char():
                    # Char is unsigned 16-bit
                    result = val if val.signs <= {0} else SignSet.from_sign("0+")
                case _:
                    raise NotImplementedError(f"Cast from int to {to} not supported")
            yield (pc + 1, after.push(result))

        case a:
            raise NotImplementedError(a.help())


def initialstate(
    bc: jpamb.Bytecode,
    methodid: jvm.AbsMethodID,
    inputs: jpamb.Input | None,
) -> dict[PC, State]:
    method = bc.getmethod(methodid)
    locals = [SignSet.bot()] * method.max_locals

    if inputs is None:
        for i, p in enumerate(methodid.extension.params):
            locals[i] = SignSet.top()
    else:
        for i, x in enumerate(inputs.values):
            match x:
                case jpamb.case.Boolean(value=value):
                    locals[i] = SignSet.abstract([StackInt(int(value))])
                case jpamb.case.Int(value=value):
                    locals[i] = SignSet.abstract([StackInt(int(value))])
                case jpamb.case.Array() | jpamb.case.String():
                    # A concrete array/string input is a non-null reference.
                    locals[i] = SignSet.from_sign("+")
                case _:
                    raise NotImplementedError(f"Unsupported value {x!r}")

    state = State(tuple(locals), ())
    return {PC(methodid, 0): state}

class Worklist:

    def __init__(self, pcs: Iterable[PC] = ()):
        self.heap: list[tuple[int, int, int, PC]] = []
        self.pending: set[PC] = set()
        self.stepped: set[PC] = set()
        self.counter = 0
        for pc in pcs:
            self.push(pc)

    def push(self, pc: PC):
        if pc in self.pending:
            return
        self.pending.add(pc)
        self.counter += 1
        key = (pc in self.stepped, pc.offset, self.counter, pc)
        heapq.heappush(self.heap, key)

    def pop(self) -> PC:
        *_, pc = heapq.heappop(self.heap)
        self.pending.remove(pc)
        self.stepped.add(pc)
        return pc

    def __contains__(self, pc: PC):
        return pc in self.pending

    def __bool__(self):
        return bool(self.heap)


@dataclass
class AbstractInterpreter:
    bc: jpamb.Bytecode
    entry: jvm.AbsMethodID
    worklist: Worklist
    states: dict[PC, State]
    callers: dict[jvm.AbsMethodID, set[PC]] = field(default_factory=dict)
    returns: dict[jvm.AbsMethodID, SignSet | None] = field(default_factory=dict)
    reported: set[tuple[PC, str]] = field(default_factory=set)

    @staticmethod
    def initial(bc: jpamb.Bytecode, methodid: jvm.AbsMethodID, inputs):
        states = initialstate(bc, methodid, inputs)
        worklist = Worklist(states.keys())

        return AbstractInterpreter(bc, methodid, worklist, states)

    def invoke(self, pc: PC, m: jvm.AbsMethodID, state: State):
        nargs = len(m.extension.params)
        if nargs:
            args, after = state.pop(nargs)
        else:
            args, after = (), state

        self.callers.setdefault(m, set()).add(pc)

        method = self.bc.getmethod(m)
        locals = tuple(args) + (SignSet.bot(),) * (method.max_locals - nargs)
        yield (PC(m, 0), State(locals, ()))

        if m in self.returns:
            ret = self.returns[m]
            yield (pc + 1, after if ret is None else after.push(ret))

    def ret(self, pc: PC, opr: jvm.Return, state: State):
        m = pc.method
        if m == self.entry:
            yield "ok"

        value = None if opr.type is None else state.pop(1)[0][0]

        if m in self.returns:
            before = self.returns[m]
            new = None if value is None else before | value
            changed = new != before
        else:
            new, changed = value, True

        if changed:
            self.returns[m] = new
            for site in self.callers.get(m, ()):
                self.worklist.push(site)

    def step(self) -> tuple[PC, set[str]]:
        pc = self.worklist.popleft()

        opr = self.bc[pc]
        print(f"Stepping {pc}:\n > {opr}", file=sys.stderr)

        state = self.states[pc]
        match opr:
            case jvm.InvokeStatic(method=m):
                results = self.invoke(pc, m, state)
                if m == pc.method:
                    results = itertools.chain(["*"], results)
            case jvm.Return():
                results = self.ret(pc, opr, state)
            case _:
                results = manystep(self.bc, pc, state)

        finals = set()

        for res in results:
            if isinstance(res, str):
                if (pc, res) not in self.reported:
                    self.reported.add((pc, res))
                    finals.add(res)
            else:
                pc_, st = res

                # A back edge (loop) or a recursive call might never
                # terminate, so soundly report "*".
                if pc_.method == pc.method and pc_.offset <= pc.offset:
                    if (pc, "*") not in self.reported:
                        self.reported.add((pc, "*"))
                        finals.add("*")

                before = self.states.get(pc_, None)
                after = st if before is None else before | st
                if before is None or after != before:
                    self.states[pc_] = after
                    self.worklist.push(pc_)

        return pc, finals


def interpret():
    """The static analysis"""
    methodid, input, steps = jpamb.getcase(
        "static",
        "1.0",
        "Cooked-Pikachu",
        ["static", "python"],
        for_science=True,
    )
    suite, eff = jpamb.setup()
    bc = jpamb.Bytecode(suite, eff, {})

    ai = AbstractInterpreter.initial(bc, methodid, input)

    x = jpamb.emit_init(ai.states)

    while steps > 0 and ai.worklist:
        pc, final = ai.step()
        for f in final:
            if steps <= 0:
                return
            jpamb.emit_step(x, pc, f, depth=1)
            steps -= 1

        if steps <= 0:
            return
        x = jpamb.emit_step(x, pc, ai.states, depth=1)
        steps -= 1


def analyse():
    """The static analysis"""

    methodid = jpamb.getmethodid(
        "static",
        "1.0",
        "Cooked-Pikachu",
        ["static", "python"],
        for_science=True,
    )

    suite, eff = jpamb.setup()
    bc = jpamb.Bytecode(suite, eff, {})

    steps = 300

    ai = AbstractInterpreter.initial(bc, methodid, None)

    final = set()
    while steps > 0 and ai.worklist:
        _pc, finals = ai.step()
        final |= finals
        steps -= 1

    for f in jpamb.QUERIES:
        if f not in final:
            print(f"{f};no")
        else:
            print(f"{f};maybe")
