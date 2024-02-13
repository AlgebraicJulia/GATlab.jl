export AlgMethod, AlgClosure, add_method!, @algebraic

using ...Util.MetaUtils

"""
A method of an AlgClosure
"""
struct AlgMethod
  context::TypeScope
  body::AlgTerm
  docstring::String
  args::Vector{LID}
  ret::Union{AlgType, Nothing}
  function AlgMethod(
    context::TypeScope,
    body::AlgTerm,
    docstring::String="",
    args::Vector{LID}=LID.(1:length(context)),
    ret::Union{AlgType, Nothing}=nothing,
  )
    new(context, body, docstring, args, ret)
  end
end

"""
A standalone, anonymous symbolic function. May have multiple methods.
"""
struct AlgClosure
  theory::GAT
  methods::Dict{AlgSorts, AlgMethod}
  function AlgClosure(
    theory::GAT,
    methods::Dict{AlgSorts, AlgMethod} = Dict{AlgSorts, AlgMethod}()
  )
    new(theory, methods)
  end
end

function add_method!(f::AlgClosure, m::AlgMethod)
  sorts = [AlgSort(getvalue(m.context, i)) for i in m.args]
  if haskey(f.methods, sorts)
    error("attempted to overload a pre-existing sort signature")
  end
  f.methods[sorts] = m
end

function (f::AlgClosure)(argvals::Any...)
  if length(f.methods) > 1 && any(!(x isa AlgTerm) for x in argvals)
    error("cannot infer type of non-AlgTerm value $x")
  end
  sorts = AlgSort[sortcheck.(Ref(f.theory), argvals)...]
  if !haskey(f.methods, sorts)
    error("no method with argument sorts $sorts found")
  end
  m = f.methods[sorts]
  if m.args != LID.(1:length(m.context))
    error("context inference not yet supported")
  end
  substitution = Dict{Ident, AlgTerm}(map(zip(getidents(m.context), [argvals...])) do (arg, val)
    if arg isa AlgTerm
      arg => val
    else
      arg => AlgTerm(Constant(val, getvalue(m.context, arg)))
    end
  end)
  substitute_term(m.body, substitution)
end

"""
This constructs an algebraic closure.

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
  AlgClosure(
    \$gat,
    \$args,
    \$ret
    __body,
  )
end
"""
macro algebraic(theorymodule, fn)
  theory = macroexpand(__module__, :($theorymodule.Meta.@theory))
  fn = parse_function(fn, :default)
  scope = fromexpr(theory, Expr(:vect, fn.args...), TypeScope)
  esc(
    Expr(
      :(=),
      fn.name,
      Expr(
        :let,
        Expr(
          :block,
          [:($n = $theorymodule.Meta.Constructors.$n) for n in nameof.(declarations(theory))]...,
          [:($(nameof(x)) = $(AlgTerm(AlgAnnot(AlgTerm(x), getvalue(scope, x))))) for x in getidents(scope)]...,
          :(__body = $(fn.impl)),
          :(__f = $AlgClosure($theory)),
          :(__m = $AlgMethod($scope, __body))
        ),
        Expr(
          :block,
          :($add_method!(__f, __m)
          )
        )
      )
    )
  )
end
