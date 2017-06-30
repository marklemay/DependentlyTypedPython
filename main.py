import inspect
import copy


# TODO: break up into separate files
# TODO: break into calculus of constructions unification

def dependent(func):
    vars, varargs, varkw, defaults, kwonlyargs, kwonlydefaults, annotations = inspect.getfullargspec(func)  # TODO prefered way to get annotations?

    # TODO: modify repr so the function shows its  type when printed
    # first construct the type
    def get_type():
        def rec(context, vars, out):
            if vars:
                head, *tail = vars

                # if type(annotations[head]) == DependentVar:
                #     context[head] = annotations[head].name
                # else:
                #     context[head] = annotations[head]
                return Π(head, annotations[head], rec(context, tail, out))
            else:
                return out

        return rec({}, vars, annotations["return"])

    func.get_type = get_type

    def type_check(scope):
        ty = func.get_type()

        # TODO: can check the bytecode so only applications and function creation are allowed

        # TODO: the rules for this are actually a little more complicated than checked for here, so this should be improved in the future


        def type_sig_symbolize(name_to_symbol, symbol_to_type, types):
            # TODO: should always return symbol or Prop or Π


            # TODO: needs a way to handle when this is an inner func in typecheck mode ve. when this is an innfer func with the intent to call.
            # probably the easiest is handle python types correctly, and ... run a partial symbolic execution?
            if types is Prop:
                return Prop
            elif isinstance(types, Symbolic):
                return types  # there is a symbolic type in scope
            elif type(types) == Π:
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

                return Π(input_symbol, input_type, output_type)
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

                assert type(ty) == Π
                assert isinstance(ty.in_name, Symbolic), "my abuse of the Π class has come back at me"
                return [ty.in_name] + rec(ty.out_ty, n - 1)
            else:
                return [ty]

        sym_ty_list = rec(full_symbolic_type, len(vars))

        symbolic_args = sym_ty_list[:-1]
        ty_ret = sym_ty_list[-1]

        sym_return = func(*symbolic_args)

        # print("expected:", ty_ret)
        # print("got:", sym_return)

        # TODO: it's a little awkward because we want to maintain the runnability of these functions
        # TODO: we will need to be able to account for applications on type arguments
        if ty_ret is Prop and isinstance(sym_return, Π):
            return True  # TODO: TODO TODO this is a horrifying simplification!  it is horribly unsound!!!!!
        elif type(sym_return) == Symbolic:
            assert sym_return.ty == ty_ret, "returned symbolic type" + str(sym_return.ty) + " != " + str(ty_ret)
            return sym_return.ty == ty_ret
        else:
            # TODO: this doesn't seem right...?
            # print(sym_return.get_type())
            # print(ty_ret)

            assert sym_return.get_type() == ty_ret, "returned NOT symbolic type" + str(sym_return.get_type()) + " != " + str(ty_ret)

            return sym_return.get_type() == ty_ret

    # func.type_check = type_check
    # print("typechecking...", get_type())
    assert type_check({})  # need to typcheck before assignment, people could cheat with recursion #TODO: need to pass the environment

    return func


####

# a type ref
class Symbolic:  # represents the canonical most general version of a given type
    # TODO: throw exceptions on equality checks, these are only equal if id are equal
    def __init__(self, name, ty):
        self.name = name
        self.ty = ty

    # TODO: will symbolically  simulate everything reasonable
    def __call__(self, *args, **kwargs):
        assert not kwargs, "kwargs not suported"
        assert type(self.ty) == Π, "application to non-function: " + str(self.ty)

        # TODO: need to handle replacement

        def recurs(ty, args):
            if args:
                assert type(ty) == Π, "application to non-function"  # TODO: slightly deviating from the python syntax

                head, *tail = args
                if type(head) == Symbolic:  # , "application of non_symbolic"

                    assert ty.in_ty is head.ty, "incorrect type application " + str(ty.in_ty) + " applied to " + str(head.ty)

                elif type(head) == DependentVar:  # TODO: this shouldn't happen any more
                    assert ty.in_ty == head.ty, "incorrect type application " + str(ty.in_ty) + " applied to " + str(head.ty)
                elif callable(head) and hasattr(head, "get_type"):
                    function_type = head.get_type()
                    assert ty.in_ty == function_type, "should check" + str(ty.in_ty) + " != " + str(function_type)
                    # print("hi")
                else:

                    assert False, "that didn't work!!!"

                # return recurs(ty.out_ty, tail)  # TODO: need to make symbolic application change the return types!!!
                return recurs(type_with_replacement(ty.in_name, head, ty.out_ty), tail)  # TODO: need to make symbolic application change the return types!!!
            else:
                return Symbolic("__", ty)  # TODO: should return self?

        return recurs(self.ty, args)

    def __str__(self):
        return "[" + str(self.name) + ":" + str(self.ty) + "]" + str(id(self))

    def __repr__(self):
        return str(self)


def type_with_replacement(replace_this, with_this, in_this):
    # assert isinstance(in_this, Symbolic), "no support for symbolic replacement yet"
    if in_this is Prop:
        return Prop
    elif in_this == replace_this:
        return with_this
    elif isinstance(in_this, Π):
        new_in_ty = type_with_replacement(replace_this, with_this, in_this.in_ty)
        new_out_ty = type_with_replacement(replace_this, with_this, in_this.out_ty)

        return Π(in_this.in_name, new_in_ty, new_out_ty)

    elif isinstance(in_this, Symbolic):
        # create a new symbolic object under the typing restrictions
        old_ty = in_this.ty

        if isinstance(old_ty, Π):  # TODO: too messy
            new_ty = type_with_replacement(replace_this, with_this, old_ty)
            return Symbolic(in_this.name, new_ty)
        else:
            return in_this

    assert False, "didn't check all cases:" + str(in_this) + ":" + str(type(in_this))


# dependent func
# TODO: better as an enum?
class Π:
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
        return beta_eq(self, other, {})  # TODO: for sure this is wrong because of beta redux


# TODO: not beta, gamma?
def beta_eq(this, other, replacement_context):
    if type(this) != Π and type(other) != Π:
        if other in replacement_context:
            return this == replacement_context[other]
        else:
            return this == other
    elif type(this) == Π and type(other) == Π:
        if beta_eq(this.in_ty, this.in_ty, replacement_context):

            new_replacement_context = copy.copy(replacement_context)
            new_replacement_context[other.in_name] = this.in_name

            return beta_eq(this.out_ty, other.out_ty, new_replacement_context)
        else:
            return False
    else:
        return False


# not a good name for a general audience
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


# TODO: we can abuse the notation way more, with slices to evoke the typing operator



