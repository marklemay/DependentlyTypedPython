from main import *


@dependent
def ident(A: Prop) -> Prop:
    return A























A = VAR("A")


@dependent
def ident(A: Prop, a: A) -> A:
    return a

























# but not

# A = VAR("A")
#
#
# @dependent
# def ident_bad(a: A) -> A:
#     return a













































A = VAR("A")
B = VAR("B")
a = VAR("a")


@dependent
def impl(A: Prop, B: Prop, a: A, a_to_b: FUNC(a, A, B)) -> B:
    return a_to_b(a)


assert impl(str, int, "hi", len) == 2, "this might seem crazy... but these are perfectly valid python functions"
assert impl("random", "nonsense", "hi", len) == 2, "for now I'm begrudgingly accepting the python convention of erasing type constraints at runtime"






















_ = VAR("_")
A = VAR("A")
B = VAR("B")
C = VAR("C")


@dependent
def cut_elim(A: Prop, B: Prop, C: Prop, a_to_b: FUNC(_, A, B), b_to_c: FUNC(_, B, C)) -> FUNC(_, A, C):
    @dependent
    def inner(a: A) -> C:
        return b_to_c(
            a_to_b(a)
        )

    return inner





















#but not
# A = VAR("A")
# B = VAR("B")
# C = VAR("C")
#
#
# @dependent
# def func2bad(A: Prop, B: Prop, C: Prop, a_to_b: FUNC(_, A, B), b_to_c: FUNC(_, B, C)) -> FUNC(_, A, C):
#     @dependent
#     def inner(a: A) -> C:
#         return b_to_c(a)
#
#     return inner


























A = VAR("A")


@dependent
def ident2(A: Prop) -> FUNC(_, A, A):
    @dependent
    def inner(a: A) -> A:
        return a

    return inner




























################################################

# now obvously we want and_def as an implicit assumption, defined in a library somewhere

# for all A,B.  A and B is a prop which means that any output created by any function that takes in A and B is achivable
# note that this funciton chould have been defined in any scope
@dependent
def and_def(A: Prop, B: Prop) -> Prop:
    Output = VAR("Output")
    AnyFunc = VAR("AnyFunc")

    return FUNC(Output, Prop,
                FUNC(AnyFunc, FUNC(_, A, FUNC(_, B, Output)),
                     Output))


A = VAR("A")
B = VAR("B")


# aa = and_def(A, B)
# print("hi")
# print(type(and_def)==function)

@dependent
def and_left_elim(A: Prop, B: Prop,
                  AandB: and_def(A, B)) -> A:
    @dependent
    def take_A_ignore_B(a: A, b: B) -> A:
        return a

    return AandB(A, take_A_ignore_B)


A = VAR("A")
B = VAR("B")


def and_intro(A: Prop, B: Prop, a: A, b: B) -> and_def(A, B):
    Output = VAR("Output")

    def any_output_any_func(Output: Prop, AnyFunc: FUNC(_, A, FUNC(_, B, Output))) -> Output:
        return AnyFunc(a, b)

    return any_output_any_func

























# type level equality
def eq_def(A: Prop, B: Prop) -> Prop:
    P = VAR("P")
    x = VAR("x")
    return FUNC(P, FUNC(_, Prop, FUNC(_, Prop, Prop)),  # any porperty
                FUNC(_, FUNC(x, Prop, P(x, x)),  # (evidence) that respects equivalence
                     P(A, B)  # will have the pair A B
                     ))


A = VAR("A")


# for all types A.  A=A
# note that this also denotes the inhabiteant refl
def proof_eq_reflexive(
        A: Prop,
) -> eq_def(A, A):
    P = VAR("P")
    x = VAR("x")

    def inner(P: FUNC(_, Prop, FUNC(_, Prop, Prop)),
              pxx: FUNC(x, Prop, P(x, x))
              ) -> P(A, A):
        return pxx(A)

    return inner


def swap_args(P: FUNC(_, Prop, FUNC(_, Prop, Prop))) -> FUNC(_, Prop, FUNC(_, Prop, Prop)):
    def inner(A: Prop, B: Prop) -> Prop:
        return P(B, A)

    return inner


A = VAR("A")
B = VAR("B")


# for all types A.  A=A
# note that this also denotes the inhabiteant refl
def proof_eq_sym(
        A: Prop, B: Prop,
        AandB: eq_def(A, B)
) -> eq_def(B, A):
    P = VAR("P")
    x = VAR("x")

    def inner(P: FUNC(_, Prop, FUNC(_, Prop, Prop)),
              pxx: FUNC(x, Prop, P(x, x))
              ) -> P(B, A):
        return AandB(swap_args(P), pxx)

    return inner

# TODO: eq transitive
