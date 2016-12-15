from main import *


A = VAR("A")
B = VAR("B")
a = VAR("a")


@dependent
def impl(A: Prop, B: Prop, a: A, a_to_b: FUNC[a: A, B]) -> B: # this abuses slice notation, but looks closer to the expected syntax
    return a_to_b(a)

# could also override the bit shift operator
@dependent
def impl(A: Prop, B: Prop, a: A, a_to_b: FUNC[a: A >> B]) -> B:
    return a_to_b(a)
