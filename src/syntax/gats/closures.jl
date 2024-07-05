export AlgMethod, AlgClosure, add_method!, @algebraic

using ...Util.MetaUtils

"""
A method of an AlgClosure. Can also be used standalone.
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
Currently does not do any sort/typechecking. AlgClosure does sort checking,
so when called via AlgClosure this works as normal.
"""
function (m::AlgMethod)(argvals::Any...)
  substitution = Dict{Ident, AlgTerm}(map(zip(getidents(m.context), [argvals...])) do (arg, val)
    if val isa AlgTerm
      arg => val
    else
      arg => Constant(val, getvalue(m.context, arg))
    end
  end)
  substitute_term(m.body, substitution)
end

"""
This implements the Dtry-algebra structure on the multicategory of types and
AlgMethods.
"""
function tcompose(ms::Dtry{AlgMethod}, argnames::Vector{Symbol})
  # First check that all methods have argument contexts of the same
  # length/variable names
  # argnames = ...
  # For now pass in argnames

  # Then create a new typescope with the same variable names, but with types
  # given by tcompose of the argument types of the ms
  contexts = map(m -> m.context, TypeScope, ms)
  context = TypeScope(
    Scope([x => tcompose(map(ctx -> getvalue(ctx, LID(i)), AlgType, contexts)) for (i,x) in enumerate(argnames)]...)
  )

  # Then for each method, create a new body by applying it to the variables
  # in the new scope with the appropriate AlgDots added
  bodies = mapwithkey(AlgTerm, ms) do k, m
    m([Var(x)[k] for x in getidents(context)]...)
  end

  # Finally, compose all of the bodies into an expression creating an
  # AlgNamedTuple
  body = Dtrys.fold(
    NamedTupleTerm(AlgNamedTuple(OrderedDict{Symbol, AlgTerm}())),
    x -> x,
    d -> NamedTupleTerm(AlgNamedTuple{AlgTerm}(d)),
    bodies
  )

  ret = try
    tcompose(map(m -> m.ret, ms))
  catch _
    nothing
  end

  AlgMethod(
    context,
    body,
    "",
    LID.(eachindex(argnames)),
    ret
  )
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

function tcompose(fs::Dtry{AlgClosure}, argnames::Vector{Symbol})
  ms = map(f -> only(values(f.methods)), fs)
  m = tcompose(ms, argnames)
  f = AlgClosure(first(fs).theory)
  add_method!(f, m)
  f
end

function (f::AlgClosure)(argvals::Any...)
  for x in argvals
    if !(x isa AlgTerm)
      error("cannot infer type of non-AlgTerm value $x")
    end
  end
  sorts = AlgSort[sortcheck.(Ref(f.theory), argvals)...]
  if !haskey(f.methods, sorts)
    error("no method with argument sorts $sorts found")
  end
  m = f.methods[sorts]
  if m.args != LID.(1:length(m.context))
    error("context inference not yet supported")
  end
  m(argvals...)
end

function Base.show(io::IO, f::AlgClosure)
  m = only(values(f.methods))
  fndef = Expr(:(->), Expr(:tuple, toexpr(f.theory, m.context).args...), toexpr(GATContext(f.theory, m.context), m.body))
  println(io, "AlgClosure in theory $(nameof(f.theory)) with definition:")
  print(io, fndef)
end

function Base.show(io::IO, m::AlgMethod; theory)
  fndef = Expr(:(->), Expr(:tuple, toexpr(theory, m.context).args...), toexpr(GATContext(theory, m.context), m.body))
  print(io, fndef)
end

function strip_annot(t::AlgTerm)
  @match t begin
    Annot(t, _) => map(strip_annot, t)
    _ => map(strip_annot, t)
  end
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

Then, we *evaluate* the body at runtime, and create the algebraic function.
This means that arbitrary Julia code can go in the body, including calling
other algebraic functions that happen to be in scope.

So, for instance, something like

```
double = true

@algebraic ThRing f(x, y)
  if double
    (x + y) + (x + y)
  else
    x + y
  end
end
```

would produce the same result as

```
@algebraic ThRing f(x, y)
  (x + y) + (x + y)
end
```
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
          [:($(nameof(x)) = $(Annot(Var(x), getvalue(scope, x)))) for x in getidents(scope)]...,
          :(__body = $strip_annot($(fn.impl))),
          :(__f = $AlgClosure($theory)),
          :(__m = $AlgMethod($scope, __body))
        ),
        Expr(
          :block,
          :($add_method!(__f, __m)),
          :__f
        )
      )
    )
  )
end
