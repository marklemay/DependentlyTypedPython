import inspect
import copy


# TODO: toss this in github....


def dependent(func):
    vars, varargs, varkw, defaults, kwonlyargs, kwonlydefaults, annotations = inspect.getfullargspec(func)  # TODO prefered way to get annotations?

    # first construct the type
    def get_type():
        def rec(context, vars, out):
            if vars:
                head, *tail = vars

                # if type(annotations[head]) == DependentVar:
                #     context[head] = annotations[head].name
                # else:
                #     context[head] = annotations[head]
                return FUNC(head, annotations[head], rec(context, tail, out))
            else:
                return out

        return rec({}, vars, annotations["return"])

    func.get_type = get_type

    def type_check(scope):
        ty = func.get_type()

        # TODO: can check the bytecode so only applications and function creation are allowed

        # TODO: the rules for this are actually a little more complicated than checked for here, so this should be improved in the future


        def type_sig_symbolize(name_to_symbol, symbol_to_type, types):
            # TODO: should always return symbol or Prop or FUNC


            # TODO: needs a way to handle when this is an inner func in typecheck mode ve. when this is an innfer func with the intent to call.
            # probably the easiest is handle python types correctly, and ... run a partial symbolic exicution?
            if types is Prop:
                return Prop
            elif isinstance(types, Symbolic):
                return types  # there is a symbolic type in scope
            elif type(types) == FUNC:
                input_type = type_sig_symbolize(name_to_symbol, symbol_to_type, types.in_ty)

                input_symbol = Symbolic(types.in_name, input_type)

                new_name_to_symbol = copy.copy(name_to_symbol)  # shallow copy
                new_symbol_to_type = copy.copy(symbol_to_type)  # shallow copy

                # assert type(types.in_name) == str, "what"
                if type(types.in_name) == str:
                    new_name_to_symbol[types.in_name] = input_symbol
                if isinstance(types.in_name, DependentVar):
                    # TODO: this is not supised to happen...?
                    new_name_to_symbol[types.in_name.name] = input_symbol

                new_symbol_to_type[input_symbol] = input_type

                output_type = type_sig_symbolize(new_name_to_symbol, new_symbol_to_type, types.out_ty)

                return FUNC(input_symbol, input_type, output_type)
            elif isinstance(types, DependentVar) and types.name in name_to_symbol:  # TODO: should be more worried about var capture
                return name_to_symbol[types.name]
            else:
                assert False, "cannot handle type " + str(types)

        full_symbolic_type = type_sig_symbolize({}, {}, ty)  # TODO: use scope

        # create arg list
        def rec(ty, n):
            if n > 0:

                # assert isinstance(ty_sym, Symbolic)
                # ty = ty_sym.ty

                assert type(ty) == FUNC
                assert isinstance(ty.in_name, Symbolic), "my abuse of the FUNC class has come back at me"
                return [ty.in_name] + rec(ty.out_ty, n - 1)
            else:
                return [ty]

        sym_ty_list = rec(full_symbolic_type, len(vars))

        symbolic_args = sym_ty_list[:-1]
        ty_ret = sym_ty_list[-1]

        sym_return = func(*symbolic_args)

        # print("expected:", ty_ret)
        # print("got:", sym_return)

        # TODO: it's a little akward becuase we want to maintain the runnability of these functions
        # TODO: we will need to be able to acount for aplications on type argumentes
        if ty_ret is Prop and isinstance(sym_return, FUNC):
            return True  # TODO: TODO TODO this is a horrifying simplification!  it is horribly unsound!!!!!
        elif type(sym_return) == Symbolic:
            return sym_return.ty == ty_ret
        else:
            # TODO: this doesn't seem right...?
            # print(sym_return.get_type())
            # print(ty_ret)

            return sym_return.get_type() == ty_ret

    # func.type_check = type_check
    # print("typechecking...", get_type())
    assert type_check({})  # need to typcheck before assignment, people could cheat with recursion #TODO: need to pass the environment

    return func


####

# a type ref
class Symbolic:
    def __init__(self, name, ty):
        self.name = name
        self.ty = ty

    # TODO: will symbolicy  simulate everythingreasonable
    def __call__(self, *args, **kwargs):
        assert not kwargs, "kwargs not suported"
        assert type(self.ty) == FUNC, "application to non-function: " + str(self.ty)

        # TODO: need to handle replacement

        def recurs(ty, args):
            if args:
                assert type(ty) == FUNC, "application to non-function"  # TODO: slightly deviating from the python syntax

                head, *tail = args
                if type(head) == Symbolic:  # , "application of non_symbolic"

                    assert ty.in_ty is head.ty, "incorrect type application " + str(ty.in_ty) + " applied to " + str(head.ty)

                elif type(head) == DependentVar:  # TODO: this shouldn't happen any more
                    assert ty.in_ty == head.ty, "incorrect type application " + str(ty.in_ty) + " applied to " + str(head.ty)
                elif callable(head) and hasattr(head, "get_type"):
                    function_type = head.get_type()
                    assert ty.in_ty == function_type, "should check"
                    print("hi")
                else:

                    assert False, "that didn't work!!!"

                return recurs(ty.out_ty, tail) #TODO: need to make symbolic aplication change the return types!!!
            else:
                return Symbolic("__", ty)

        return recurs(self.ty, args)

    def __str__(self):
        return "[" + str(self.name) + ":" + str(self.ty) + "]" + str(id(self))

    def __repr__(self):
        return str(self)


# dependent func
# TODO: better as an enum?
class FUNC:
    def __init__(self, in_name, in_ty, out_ty):
        self.in_name = in_name
        self.in_ty = in_ty
        self.out_ty = out_ty

    def __str__(self):
        return ("("
                + str(self.in_name) + ":"
                + str(self.in_ty) + "->"
                + str(self.out_ty) + ")")

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        return beta_eq(self, other, {})  # TODO: for sure this is wron becuase of beta redux


def beta_eq(this, other, replacement_context):
    if type(this) != FUNC and type(other) != FUNC:
        if other in replacement_context:
            return this == replacement_context[other]
        else:
            return this == other
    elif type(this) == FUNC and type(other) == FUNC:
        if beta_eq(this.in_ty, this.in_ty, replacement_context):

            new_replacement_context = copy.copy(replacement_context)
            new_replacement_context[other.in_name] = this.in_name

            return beta_eq(this.out_ty, other.out_ty, new_replacement_context)
        else:
            return False
    else:
        return False

    return False


# not a good name for a general audiance
class Prop:
    # TODO: need type clesses for this to work
    def __str__(self):
        return "*"

    def __repr__(self):
        return str(self)


class DependentVar:
    def __init__(self, *args, **kwargs):
        self.name = "?????"
        pass

    def __call__(self, *args, **kwargs):
        return DependentVar()

    def __str__(self):
        if self.name:
            return "'" + self.name + "'"
        else:
            return "'????'"

    def __repr__(self):
        return str(self)


def VAR(name):
    var = DependentVar()
    var.name = name
    return var


# bad abuse of notation

_ = VAR("_")


# TODO: we can abuse the notaiton way more, with slices to evoke the tyoing operator















####################################################################################################

# questions for hongwie
# is this already a thing?
# obvous limitations
# write up plan, can compare and contrast 3 different aproaches to reasoning about python, given CPython. at least shallowly

# TODO: need some test cases around beta reduction

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

A = VAR("A")
B = VAR("B")
a = VAR("a")


@dependent
def impl(A: Prop, B: Prop, a: A, a_to_b: FUNC(a, A, B)) -> B:
    return a_to_b(a)


assert impl(str, int, "hi", len) == 2, "this might seem crazy... but these are perfectly valid python functions"
assert impl(_, _, "hi", len) == 2, "for now I'm begrudgingly accepting the python convention of erasing type constraints at runtime"

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


# unfortunately there is still a bug about inner functions, that try to create themselves in type check mode
# assert cut_elim(str, int, str, len, lambda n: "is " + str(n) + " chars long")(
#     "some string") == 2, "this might seem crazy... but these are perfectly valid python functions"

try:
    A = VAR("A")
    B = VAR("B")
    C = VAR("C")


    @dependent
    def func2bad(A: Prop, B: Prop, C: Prop, a_to_b: FUNC(_, A, B), b_to_c: FUNC(_, B, C)) -> FUNC(_, A, C):
        @dependent
        def inner(a: A) -> C:
            return b_to_c(a)

        return inner


except:
    pass
else:
    assert False, "should throw error"

# This would be a cool feature. Doesn't work right now

# A = VAR("A")
#
# @dependent
# def ident_self() -> FUNC(A, Prop, FUNC(_, A, A)):
#     return ident(ident.get_type(), ident)


A = VAR("A")


@dependent
def ident2(A: Prop) -> FUNC(_, A, A):
    @dependent
    def inner(a: A) -> A:
        return a

    return inner


# This would be a cool feature. Doesn't work right now

# A = VAR("A")
#
#
# @dependent
# def ident_self_partial() -> FUNC(_, FUNC(A, Prop, FUNC(_, A, A)), FUNC(A, Prop, FUNC(_, A, A))):
#     return ident(ident.get_type())

#
#
# A = DependentVar()
# B = DependentVar()
#
#
# # make sure beta reduction is cool
# def ident_self_partial2() -> FUNC(_, FUNC(A, Prop, FUNC(_, A, A)), FUNC(B, Prop, FUNC(_, B, B))):
#     return ident(ident.get_type())





# # TODO: now obvously we want and_def as an implicit assumption, defined in a library somewhere
# # for all A,B.  A and B is a prop which means that any output created by any function that takes in A and B is achivable
# # note that this funciton chould have been defined in any scope
# @dependent
# def and_def(A: Prop, B: Prop) -> Prop:
#     Output = VAR("Output")
#     AnyFunc = VAR("AnyFunc")
#
#     return FUNC(Output, Prop,
#                 FUNC(AnyFunc, FUNC(_, A, FUNC(_, B, Output)),
#                      Output))
#
#
# A = VAR("A")
# B = VAR("B")
#
#
# # aa = and_def(A, B)
# # print("hi")
# # print(type(and_def)==function)
#
# @dependent
# def and_left_elim(A: Prop, B: Prop,
#                   AandB: and_def(A, B)) -> A:  # TODO: need to handle the super akward case where, dependent vars are computed on (could lead to unsoundness)
#     @dependent
#     def take_A_ignore_B(a: A, b: B) -> A:
#         return a
#
#     return AandB(A, take_A_ignore_B)

#
# A = DependentVar()
# B = DependentVar()
#
#
# def and_intro(A: Prop, B: Prop, a: A, b: B) -> and_def(A, B):
#     Output = DependentVar()
#
#     def any_output_any_func(Output: Prop, AnyFunc: FUNC(_, A, FUNC(_, B, Output))) -> Output:
#         return AnyFunc(a, b)
#
#     return any_output_any_func
#
#
# # type level equality
# def eq_def(A: Prop, B: Prop) -> Prop:
#     P = DependentVar()
#     x = DependentVar()
#     return FUNC(P, FUNC(_, Prop, FUNC(_, Prop, Prop)),  # any porperty
#                 FUNC(_, FUNC(x, Prop, P(x, x)),  # (evidence) that respects equivelence
#                      P(A, B)  # will have the pair A B
#                      ))
#
#
# A = DependentVar()
#
#
# # for all types A.  A=A
# # note that this also denotes the inhabiteant refl
# def proof_eq_reflexive(
#         A: Prop,
# ) -> eq_def(A, A):
#     P = DependentVar()
#     x = DependentVar()
#
#     def inner(P: FUNC(_, Prop, FUNC(_, Prop, Prop)),
#               pxx: FUNC(x, Prop, P(x, x))  # TODO: rename pcc
#               ) -> P(A, A):
#         return pxx(A)
#
#     return inner
#
#
# def swap_args(P: FUNC(_, Prop, FUNC(_, Prop, Prop))) -> FUNC(_, Prop, FUNC(_, Prop, Prop)):
#     def inner(A: Prop, B: Prop) -> Prop:
#         return P(B, A)
#
#     return inner
#
#
# A = DependentVar()
# B = DependentVar()
#
#
# # for all types A.  A=A
# # note that this also denotes the inhabiteant refl
# def proof_eq_sym(
#         A: Prop, B: Prop,
#         AandB: eq_def(A, B)
# ) -> eq_def(B, A):
#     P = DependentVar()
#     x = DependentVar()
#
#     def inner(P: FUNC(_, Prop, FUNC(_, Prop, Prop)),
#               pxx: FUNC(x, Prop, P(x, x))  # TODO: rename pcc
#               ) -> P(B, A):
#         return AandB(swap_args(P), pxx)
#
#     return inner
#
# #TODO: eq transitive
#
#
