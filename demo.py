from main import *


# this library embeds a dependent type system into standard python (3.5)
# dependent types can be used to structure programs and as a foundational mathematical theory
# technically these types should be equivalent to the Calculus of Constructions,
# http://www.sciencedirect.com/science/article/pii/0890540188900053


# The calculus of constructions contains one constant "Prop" which represents the collection of all types,
# we can use it in python's type hints to like this:
def ident(A: Prop) -> Prop:
    return A


# but python will not typecheck this function automatically. To typecheck the function when it is declared we need to
# use the @dependent annotation
@dependent
def ident(A: Prop) -> Prop:
    return A


assert ident(int) == int, "all functions declared with @dependent should work just fine as a python functions"

# In order to make use of dependent types in syntactically valid python we need to register them before hand
# we do this with VAR
A = VAR("A")


# Now we can define a simple dependently typed function
@dependent
def ident(A: Prop, a: A) -> A:
    return a


# it is dependent because the output relies on the input of the first parameter

assert ident(str, "hi") == "hi", "the function runs as you would expect"
assert type(ident(str, "hi")) == str, "when the first parameter is a string the function returns a string"
assert type(ident(int, 7)) == int, "when the first parameter is a int the function returns a int"

assert type(ident("not a type", 7)) == int, ("for now I'm begrudgingly accepting the python convention of erasing type "
                                             "constraints at runtime")

# the Calculus of Constructions is not merely about defining functions but corresponds to a rich theory of
# mathematical logic,
# ident represents a proof that "For all A, A implies A".

# A type checker should actually check your types,
# you can prove this is happening by uncommenting the code below and running the file

# A = VAR("A")
#
#
# @dependent
# def ident_bad(a: A) -> A:
#     return a

# it doesn't typecheck because A is not defined on the scope of the function


# now sometimes we want to use functions as inputs, but python limits us
# we cannot use the syntax ":" and "->" as freely as we would like
# We need to construct our function types with FUNC,
# FUNC takes 3 arguments, the name of the first input, the type of the fist input and the type of the output

# the type signature of the ident function is
# FUNC(A, Prop, FUNC( a, A,  A))
# note that the function signature makes the dependency on A clear

# we can make more complicated functions/proofs

A = VAR("A")
B = VAR("B")
a = VAR("a")


@dependent
def impl(A: Prop, B: Prop, a: A, a_to_b: FUNC(a, A, B)) -> B:
    return a_to_b(a)


assert impl(str, int, "hi", len) == 2, "this might seem crazy... but these are perfectly valid python functions"
# and again this serves as a proof of "For all A, For all B, (A and (A implies B)) implies B"

# I will use th common convection of using _ in place of variables that don't need names
_ = VAR("_")


# with this in mind the above function could be written as
@dependent
def impl(A: Prop, B: Prop, a: A, a_to_b: FUNC(_, A, B)) -> B:
    return a_to_b(a)


# since the B did not depend on the specific a in FUNC(a, A, B)


# we can write even more complicated functions/proofs with inner functions
# that allows us to "assume things"
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


# this leaves us with more to check from out type checker

# Should error:
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


# implication is fine but we can define other logical primitives in a functional way
# take AND for instance
# how can AND be defined with just functions?

# ...

# we want to say that if we have "A AND B" we can get any output from any function that takes A and B.
# more formally:
@dependent
def and_def(A: Prop, B: Prop) -> Prop:
    Output = VAR("Output")
    AnyFunc = VAR("AnyFunc")

    return FUNC(Output, Prop,
                FUNC(AnyFunc, FUNC(_, A, FUNC(_, B, Output)),  # the function AnyFunc takes an A and a B
                     Output))

# note that this function could have been defined in any scope, and it returns a type signature (
# which itself has type Prop)

# (obviously this should be defined in a library somewhere)


# we can define some of the essential properties of AND definition
# like "A AND B implies A"
A = VAR("A")
B = VAR("B")


@dependent
def and_left_elim(A: Prop, B: Prop,
                  AandB: and_def(A, B)) -> A:
    @dependent
    def take_A_ignore_B(a: A, b: B) -> A:
        return a

    return AandB(A, take_A_ignore_B)
# take some time to understand this, the trick is really cool
# A is given as the type of output


# A implies (B implies A AND B)
A = VAR("A")
B = VAR("B")


def and_intro(A: Prop, B: Prop, a: A, b: B) -> and_def(A, B):
    Output = VAR("Output")

    def any_output_any_func(Output: Prop, AnyFunc: FUNC(_, A, FUNC(_, B, Output))) -> Output:
        return AnyFunc(a, b)

    return any_output_any_func


# We can also define type level equality
def eq_def(A: Prop, B: Prop) -> Prop:
    P = VAR("P")
    x = VAR("x")
    return FUNC(P, FUNC(_, Prop, FUNC(_, Prop, Prop)),  # any porperty
                FUNC(_, FUNC(x, Prop, P(x, x)),  # (evidence) that respects equivalence
                     P(A, B)  # will have the pair A B
                     ))


A = VAR("A")


# for all types A.  A=A
# note that this also denotes the inhabitant refl
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


# for all types A, B.  A=B implies B=A
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
