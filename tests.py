from main import *


####################################################################################################


# TODO: need some test cases around beta reduction
# TODO: need some test cases around renaming equivelence

@dependent
def ident(A: Prop) -> Prop:
    return A


A = VAR("A")


@dependent
def ident(A: Prop, a: A) -> A:
    return a


# but not
try:

    A = VAR("A")


    @dependent
    def ident_bad(a: A) -> A:
        return a
except:
    pass
else:
    assert False, "should throw error"

try:
    A = VAR("A")


    @dependent
    def ident_bad(A: Prop, a: Prop) -> A:
        return a
except:
    pass
else:
    assert False, "should throw error"

try:
    A = VAR("A")


    @dependent
    def ident_bad(A: Prop, a: A) -> Prop:
        return a
except:
    pass
else:
    assert False, "should throw error"

try:
    A = VAR("A")


    @dependent
    def ident_bad(A: Prop, a: A) -> A:
        return A
except:
    pass
else:
    assert False, "should throw error"

#############################################






















_ = VAR("_")

A = VAR("A")
B = VAR("B")
a = VAR("a")


@dependent
def impl(A: Prop, B: Prop, a: A, a_to_b: Σ(a, A, B)) -> B:
    return a_to_b(a)


assert impl(str, int, "hi", len) == 2, "this might seem crazy... but these are perfectly valid python functions"
assert impl(_, _, "hi", len) == 2, "for now I'm begrudgingly accepting the python convention of erasing type constraints at runtime"

A = VAR("A")
B = VAR("B")
C = VAR("C")


@dependent
def cut_elim(A: Prop, B: Prop, C: Prop, a_to_b: Σ(_, A, B), b_to_c: Σ(_, B, C)) -> Σ(_, A, C):
    @dependent
    def inner(a: A) -> C:
        return b_to_c(
            a_to_b(a)
        )

    return inner


try:
    A = VAR("A")
    B = VAR("B")
    C = VAR("C")


    @dependent
    def func2bad(A: Prop, B: Prop, C: Prop, a_to_b: Σ(_, A, B), b_to_c: Σ(_, B, C)) -> Σ(_, A, C):
        @dependent
        def inner(a: A) -> C:
            return b_to_c(a)

        return inner


except:
    pass
else:
    assert False, "should throw error"

A = VAR("A")


@dependent
def ident2(A: Prop) -> Σ(_, A, A):
    @dependent
    def inner(a: A) -> A:
        return a

    return inner


################################################

# TODO: now obvously we want and_def as an implicit assumption, defined in a library somewhere
# for all A,B.  A and B is a prop which means that any output created by any function that takes in A and B is achivable
# note that this funciton chould have been defined in any scope
@dependent
def and_def(A: Prop, B: Prop) -> Prop:
    Output = VAR("Output")
    AnyFunc = VAR("AnyFunc")

    return Σ(Output, Prop,
                Σ(AnyFunc, Σ(_, A, Σ(_, B, Output)),
                     Output))


A = VAR("A")
B = VAR("B")


# aa = and_def(A, B)
# print("hi")
# print(type(and_def)==function)

@dependent
def and_left_elim(A: Prop, B: Prop,
                  AandB: and_def(A, B)) -> A:
    # TODO: need to handle the super akward case where, dependent vars are computed on (could lead to unsoundness)(?)
    @dependent
    def take_A_ignore_B(a: A, b: B) -> A:
        return a

    return AandB(A, take_A_ignore_B)


A = VAR("A")
B = VAR("B")


def and_intro(A: Prop, B: Prop, a: A, b: B) -> and_def(A, B):
    Output = VAR("Output")

    def any_output_any_func(Output: Prop, AnyFunc: Σ(_, A, Σ(_, B, Output))) -> Output:
        return AnyFunc(a, b)

    return any_output_any_func


# type level equality
def eq_def(A: Prop, B: Prop) -> Prop:
    P = VAR("P")
    x = VAR("x")
    return Σ(P, Σ(_, Prop, Σ(_, Prop, Prop)),  # any porperty
                Σ(_, Σ(x, Prop, P(x, x)),  # (evidence) that respects equivelence
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

    def inner(P: Σ(_, Prop, Σ(_, Prop, Prop)),
              pxx: Σ(x, Prop, P(x, x))  # TODO: rename pcc
              ) -> P(A, A):
        return pxx(A)

    return inner


def swap_args(P: Σ(_, Prop, Σ(_, Prop, Prop))) -> Σ(_, Prop, Σ(_, Prop, Prop)):
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

    def inner(P: Σ(_, Prop, Σ(_, Prop, Prop)),
              pxx: Σ(x, Prop, P(x, x))  # TODO: rename pcc
              ) -> P(B, A):
        return AandB(swap_args(P), pxx)

    return inner

# TODO: eq transitive
