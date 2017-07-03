# the biggest bug is that I didn't call this "ΠPython" that should be fixed first.


from main import *
from tests import *

_ = VAR("_")

A = VAR("A")
a = VAR("a")

# equivalence under renaming
@dependent
def ident() -> Π(A, Prop, Π(a, A, A)):
    B = VAR("B")

    @dependent
    def inner_ident(B: Prop, b: B) -> B:
        return a

    return inner_ident


# right now Prop typechecks cheats, should fail because output is called before it is used
@dependent
def and_def(A: Prop, B: Prop) -> Prop:
    Output = VAR("Output")
    AnyFunc = VAR("AnyFunc")
    C = VAR("C")

    return Π(C, Prop,
                Π(AnyFunc, Π(_, A, Π(_, B, Output)),
                     Output))


# TODO: should disallow unsupported operations
A = VAR("A")


@dependent
def ident(A: Prop) -> A:
    while True:
        pass
    return


A = VAR("A")
B = VAR("B")
C = VAR("C")


@dependent
def cut_elim(A: Prop, B: Prop, C: Prop, a_to_b: Π(_, A, B), b_to_c: Π(_, B, C)) -> Π(_, A, C):
    @dependent
    def inner(a: A) -> C:
        return b_to_c(
            a_to_b(a)
        )

    return inner


# unfortunately there is still a bug about inner functions, that try to create themselves in type check mode, even when called with non symbolic input
assert cut_elim(str, int, str, len, lambda n: "is " + str(n) + " chars long")(
    "some string") == 2, "this might seem crazy... but these are perfectly valid python functions"


# it might be nice to assume anything that in scope should be type checked
@dependent
def cut_elim(A: Prop, B: Prop, C: Prop, a_to_b: Π(_, A, B), b_to_c: Π(_, B, C)) -> Π(_, A, C):
    def inner(a: A) -> C:
        return b_to_c(
            a_to_b(a)
        )

    return inner


# This would be a cool feature. Doesn't work right now

A = VAR("A")


@dependent
def ident_self() -> Π(A, Prop, Π(_, A, A)):
    return ident(ident.get_type(), ident)


# This would be a cool feature. Doesn't work right now

A = VAR("A")


@dependent
def ident_self_partial() -> Π(_, Π(A, Prop, Π(_, A, A)), Π(A, Prop, Π(_, A, A))):
    return ident(ident.get_type())


A = VAR("A")
B = VAR("B")


# make sure beta reduction is cool
def ident_self_partial2() -> Π(_, Π(A, Prop, Π(_, A, A)), Π(B, Prop, Π(_, B, B))):
    return ident(ident.get_type())
