module AlgebraicFunctions

"""

"""
struct AlgebraicFunction
  theory::GAT
  args::TypeScope
  ret::AlgType
  body::AlgTerm
  docstring::String
  function AlgebraicFunction(theory::GAT, args::TypeScope, ret::AlgType, body::AlgTerm, docstring::String="")
    new(theory, args, ret, body, docstring)
  end
end

function (f::AlgebraicFunction)(argvals::Any...)
  substitution = Dict{Ident, AlgTerm}(map(zip(idents(f.args), argvals)) do (arg, val)
    if arg isa AlgTerm
      sortcheck(f.theory, val) == AlgSort(getvalue(f.args, arg)) || error("sort of argument $arg does not match $val")
      arg => val
    else
      arg => AlgConstant(val, getvalue(f.args, arg))
    end
  end)
  substitute_term(f.body, substitution)
end

"""
This constructs an algebraic function.

Use:

```julia
@algebraic ThRing f(x, y)
  x^2 + 2*x*y + y^2
end
```

This expands in the following way.

First, we create an outer let binding that binds all declarations in the theory to
the term-creating functions defined in the theory. So this would look something like:

```
let
  + = ThRing.Meta.Constructors.+
  * = ThRing.Meta.Constructors.*
  ...
end
```

Then, we bind the arguments to the function

```
let
  ...
  x = AlgTerm(\$(ident(args; name=:x)))
  y = AlgTerm(\$(ident(args; name=:y)))
  ...
end
```

Here `args` is a TypeScope that we generate by parsing the arguments to `fn`.

Finally, we *evaluate* the body at runtime, and create the algebraic function.
This means that arbitrary Julia code can go in the body, including calling
other algebraic functions that happen to be in scope.

Also, the result of this let block is bound to the name given to the function.

```
\$name = let
  ...
  __body = \$body
  AlgebraicFunction(
    \$gat,
    \$args,
    \$ret
    __body,
  )
end
"""
macro algebraic(theorymodule, fn)

end

end
