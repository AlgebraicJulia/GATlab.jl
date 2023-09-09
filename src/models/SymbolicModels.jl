module SymbolicModels
export GATExpr, @symbolic_model, SyntaxDomainError

using ...Syntax

using Base.Meta: ParseError
using MLStyle

# Data types
############

""" Base type for expressions in the syntax of a GAT. This is an alternative
to `AlgTerm` used for backwards compatibility with Catlab.

We define Julia types for each *type constructor* in the theory, e.g., object,
morphism, and 2-morphism in the theory of 2-categories. Of course, Julia's
type system does not support dependent types, so the type parameters are
incorporated in the Julia types. (They are stored as extra data in the
expression instances.)

The concrete types are structurally similar to the core type `Expr` in Julia.
However, the *term constructor* is represented as a type parameter, rather than
as a `head` field. This makes dispatch using Julia's type system more
convenient.
"""
abstract type GATExpr{T} end

head(::GATExpr{T}) where T = T
args(expr::GATExpr) = expr.args
Base.first(expr::GATExpr) = first(args(expr))
Base.last(expr::GATExpr) = last(args(expr))
gat_typeof(expr::GATExpr) = nameof(typeof(expr))
gat_type_args(expr::GATExpr) = expr.type_args


""" Get name of GAT generator expression as a `Symbol`.

If the generator has no name, returns `nothing`.
"""
function Base.nameof(expr::GATExpr{:generator})
  name = first(expr)
  isnothing(name) ? nothing : Symbol(name)
end

function Base.:(==)(e1::GATExpr{T}, e2::GATExpr{S}) where {T,S}
  T == S && e1.args == e2.args && e1.type_args == e2.type_args
end

function Base.hash(e::GATExpr, h::UInt)
  hash(args(e), hash(head(e), h))
end

function Base.show(io::IO, expr::GATExpr)
  print(io, head(expr))
  print(io, "(")
  join(io, args(expr), ",")
  print(io, ")")
end

function Base.show(io::IO, expr::GATExpr{:generator})
  print(io, first(expr))
end

function Base.show(io::IO, ::MIME"text/plain", expr::GATExpr)
  show_unicode(io, expr)
end

function Base.show(io::IO, ::MIME"text/latex", expr::GATExpr)
  print(io, "\$")
  show_latex(io, expr)
  print(io, "\$")
end

struct SyntaxDomainError <: Exception
  constructor::Symbol
  args::Vector
end

function Base.showerror(io::IO, exc::SyntaxDomainError)
  print(io, "Domain error in term constructor $(exc.constructor)(")
  join(io, exc.args, ",")
  print(io, ")")
end

# Syntax
########

"""
This is backwards compatible with the @syntax macro in Catlab

@symbolic_model FreeCategory{ObExr, HomExpr} ThCategory begin
end

```julia
module FreeCategory
export Ob,Hom
using ..__module__

theory() = ThCategory

struct Ob{T} <: ObExpr{T} # T is :generator or a Symbol
  args::Vector
  type_args::Vector{GATExpr}
end

struct Hom{T} <: HomExpr{T}
  args::Vector
  type_args::Vector{GATExpr}
end

# default implementations 

function ThCategory.dom(x::Hom)::Ob
  x.type_args[1]
end

function Ob(::Typ{Ob}, __value__::Any)::Ob
  Ob{:generator}([__value__], [])
end

function ThCategory.id(A::Ob)::Hom
  Hom{:id}([A], [A, A])
end

end #module
```
"""

function symbolic_struct(name, abstract_type, parentmod)::Expr
  quote
    struct $(esc(name)){T} <: $parentmod.$(abstract_type){T}
      args::$(Vector)
      type_args::$(Vector){$(GlobalRef(SymbolicModels, :GATExpr))}
    end
  end
end

function symbolic_structs(theory::GAT, abstract_types, parentmod)::Vector{Expr}
  Expr[
    symbolic_struct(nameof(X), abstract_type, parentmod)
    for (X, abstract_type) in zip(theory.typecons, abstract_types)
  ]
end

function symbolic_accessor(theoryname, argname, typename, rettypename, argindex, parentmod)
  quote
    function $parentmod.$theoryname.$argname(x::$(esc(typename)))::$(rettypename)
      x.type_args[$argindex]
    end
  end
end

function symbolic_accessors(theoryname, theory::GAT, parentmod)::Vector{Expr}
  Expr[
    symbolic_accessor(theoryname, nameof(binding), nameof(X), typename(theory, getvalue(binding)), i, parentmod)
    for X in typecons(theory) for (i, binding) in enumerate(getvalue(theory[X]).args)
  ]
end

function typename(theory::GAT, type::AlgType)
  esc(nameof(sortname(theory, type)))
end

function symbolic_constructor(theoryname, name::Ident, termcon::AlgTermConstructor, theory::GAT, parentmod)
  eqs = equations(termcon.args, termcon.localcontext, theory)
  eq_exprs = Expr[]

  theorymodule = :($parentmod.$theoryname)
  for expr_set in values(eqs)
    exprs = build_infer_expr.(Ref(theorymodule), [expr_set...])
    for (a, b) in zip(exprs, exprs[2:end])
      errexpr = Expr(:call, throw, Expr(:call, GlobalRef(SymbolicModels, :SyntaxDomainError),
                     Expr(:quote, nameof(name)),
                     Expr(:vect, nameof.(termcon.args)...)))

      push!(eq_exprs, Expr(:(||), Expr(:call, :(==), a, b), errexpr))
    end
  end

  expr_lookup = Dict{Reference, Any}(
    [Reference(x) => build_infer_expr(theorymodule, first(eqs[x]))
     for x in [idents(termcon.args)..., idents(termcon.localcontext)...]]
  )

  quote
    function $theorymodule.$(nameof(name))(
      $([Expr(:(::), nameof(binding), typename(theory, getvalue(binding)))
         for binding in termcon.args]...)
    )
      $(eq_exprs...)
      $(typename(theory, termcon.type)){$(Expr(:quote, nameof(name)))}(
        $(Expr(:vect, nameof.(termcon.args)...)),
        $(Expr(:ref, GlobalRef(SymbolicModels, :GATExpr),
          [compile(theorymodule, expr_lookup, arg) for arg in termcon.type.args]...))
      )
    end
  end
end

function symbolic_constructors(theoryname, theory::GAT, parentmod)::Vector{Expr}
  Expr[
    symbolic_constructor(theoryname, x, getvalue(theory[x]), theory, parentmod)
    for x in termcons(theory)
  ]
end

macro symbolic_model(decl, theoryname, body)
  theory = macroexpand(__module__, :($theoryname.@theory))
  
  (name, abstract_types) = @match decl begin
    Expr(:curly, name, abstract_types...) => (name, abstract_types)
    _ => throw(ParseError("Ill-formed head of @symbolic_model $decl"))
  end

  structs = symbolic_structs(theory, abstract_types, __module__)

  accessors = symbolic_accessors(theoryname, theory, __module__)

  constructors = symbolic_constructors(theoryname, theory, __module__)

  Expr(:toplevel,
    :(module $(esc(name))
      using ..($(nameof(__module__)))
      import ..($(nameof(__module__))): $theoryname
      const $(esc(:THEORY_MODULE)) = $(esc(theoryname))

      $(structs...)

      $(accessors...)

      $(constructors...)
    end)
  )
end

# Reflection
############

""" Invoke a term constructor by name in a syntax system.

This method provides reflection for syntax systems. In everyday use the generic
method for the constructor should be called directly, not through this function.

FIXME
"""
function invoke_term(syntax_module::Module, constructor_name::Symbol, args...)
  theory_type = syntax_module.theory()
  theory = GAT.theory(theory_type)
  syntax_types = Tuple(getfield(syntax_module, cons.name) for cons in theory.types)
  invoke_term(theory_type, syntax_types, constructor_name, args...)
end

""" Name of constructor that created expression.
"""
constructor_name(expr::GATExpr) = head(expr)
constructor_name(expr::GATExpr{:generator}) = gat_typeof(expr)

""" Create generator of the same type as the given expression.

FIXME
"""
function generator_like(expr::GATExpr, value)::GATExpr
  invoke_term(syntax_module(expr), gat_typeof(expr),
              value, gat_type_args(expr)...)
end

"""
As with [generator_like](@ref), but change the syntax instead of the name.
FIXME
"""
function generator_switch_syntax(syntax::Module,expr::GATExpr)::GATExpr
  invoke_term(syntax, gat_typeof(expr),
              nameof(expr), map(x->generator_switch_syntax(syntax,x),gat_type_args(expr))...)
end

"""
Get syntax module of given expression.
"""
syntax_module(expr::GATExpr) = parentmodule(typeof(expr))

# Functors
##########

""" Functor from GAT expression to GAT instance.

Strictly speaking, we should call these "structure-preserving functors" or,
better, "model homomorphisms of GATs". But this is a category theory library,
so we'll go with the simpler "functor".

A functor is completely determined by its action on the generators. There are
several ways to specify this mapping:

  1. Specify a Julia instance type for each GAT type, using the required `types`
     tuple. For this to work, the generator constructors must be defined for the
     instance types.

  2. Explicitly map each generator term to an instance value, using the
     `generators` dictionary.

  3. For each GAT type (e.g., object and morphism), specify a function mapping
     generator terms of that type to an instance value, using the `terms`
     dictionary.

The `terms` dictionary can also be used for special handling of non-generator
expressions. One use case for this capability is defining forgetful functors,
which map non-generators to generators.

FIXME
"""
function functor(types::Tuple, expr::GATExpr;
                 generators::AbstractDict=Dict(), terms::AbstractDict=Dict())
  # Special case: look up a specific generator.
  if head(expr) == :generator && haskey(generators, expr)
    return generators[expr]
  end

  # Special case: look up by type of term (usually a generator).
  name = constructor_name(expr)
  if haskey(terms, name)
    return terms[name](expr)
  end

  # Otherwise, we need to call a term constructor (possibly for a generator).
  # Recursively evalute the arguments.
  term_args = []
  for arg in args(expr)
    if isa(arg, GATExpr)
      arg = functor(types, arg; generators=generators, terms=terms)
    end
    push!(term_args, arg)
  end

  # Invoke the constructor in the codomain category!
  theory_type = syntax_module(expr).theory()
  invoke_term(theory_type, types, name, term_args...)
end

# Serialization
###############

""" Serialize expression as JSON-able S-expression.

The format is an S-expression encoded as JSON, e.g., "compose(f,g)" is
represented as ["compose", f, g].
"""
function to_json_sexpr(expr::GATExpr; by_reference::Function = x->false)
  if head(expr) == :generator && by_reference(first(expr))
    to_json_sexpr(first(expr))
  else
    [ string(constructor_name(expr));
      [ to_json_sexpr(arg; by_reference=by_reference) for arg in args(expr) ] ]
  end
end
to_json_sexpr(x::Union{Bool,Real,String,Nothing}; kw...) = x
to_json_sexpr(x; kw...) = string(x)

""" Deserialize expression from JSON-able S-expression.

If `symbols` is true (the default), strings are converted to symbols.
"""
function parse_json_sexpr(syntax_module::Module, sexpr;
    parse_head::Function = identity,
    parse_reference::Function = x->error("Loading terms by name is disabled"),
    parse_value::Function = identity,
    symbols::Bool = true,
  )
  theory_type = syntax_module.theory()
  theory = GAT.theory(theory_type)
  type_lens = Dict(cons.name => length(cons.params) for cons in theory.types)

  function parse_impl(sexpr::Vector, ::Type{Val{:expr}})
    name = Symbol(parse_head(symbols ? Symbol(sexpr[1]) : sexpr[1]))
    nargs = length(sexpr) - 1
    args = map(enumerate(sexpr[2:end])) do (i, arg)
      arg_kind = ((i == 1 && get(type_lens, name, nothing) == nargs-1) ||
                  arg isa Union{Bool,Number,Nothing}) ? :value : :expr
      parse_impl(arg, Val{arg_kind})
    end
    invoke_term(syntax_module, name, args...)
  end
  parse_impl(x, ::Type{Val{:value}}) = parse_value(x)
  parse_impl(x::String, ::Type{Val{:expr}}) =
    parse_reference(symbols ? Symbol(x) : x)
  parse_impl(x::String, ::Type{Val{:value}}) =
    parse_value(symbols ? Symbol(x) : x)

  parse_impl(sexpr, Val{:expr})
end

# Pretty-print
##############

""" Show the syntax expression as an S-expression.

Cf. the standard library function `Meta.show_sexpr`.
"""
show_sexpr(expr::GATExpr) = show_sexpr(stdout, expr)

function show_sexpr(io::IO, expr::GATExpr)
  if head(expr) == :generator
    print(io, repr(first(expr)))
  else
    print(io, "(")
    join(io, [string(head(expr));
              [sprint(show_sexpr, arg) for arg in args(expr)]], " ")
    print(io, ")")
  end
end

""" Show the expression in infix notation using Unicode symbols.
"""
show_unicode(expr::GATExpr) = show_unicode(stdout, expr)
show_unicode(io::IO, x::Any; kw...) = show(io, x)

function show_unicode(io::IO, expr::GATExpr; kw...)
  # By default, show in prefix notation.
  print(io, head(expr))
  print(io, "{")
  join(io, [sprint(show_unicode, arg) for arg in args(expr)], ",")
  print(io, "}")
end

function show_unicode(io::IO, expr::GATExpr{:generator}; kw...)
  print(io, first(expr))
end

function show_unicode_infix(io::IO, expr::GATExpr, op::String;
                            paren::Bool=false)
  show_unicode_paren(io, expr) = show_unicode(io, expr; paren=true)
  if (paren) print(io, "(") end
  join(io, [sprint(show_unicode_paren, arg) for arg in args(expr)], op)
  if (paren) print(io, ")") end
end

""" Show the expression in infix notation using LaTeX math.

Does *not* include `\$` or `\\[begin|end]{equation}` delimiters.
"""
show_latex(expr::GATExpr) = show_latex(stdout, expr)
show_latex(io::IO, sym::Symbol; kw...) = print(io, sym)
show_latex(io::IO, x::Any; kw...) = show(io, x)

function show_latex(io::IO, expr::GATExpr; kw...)
  # By default, show in prefix notation.
  print(io, "\\mathop{\\mathrm{$(head(expr))}}")
  print(io, "\\left[")
  join(io, [sprint(show_latex, arg) for arg in args(expr)], ",")
  print(io, "\\right]")
end

function show_latex(io::IO, expr::GATExpr{:generator}; kw...)
  # Try to be smart about using text or math mode.
  content = string(first(expr))
  if all(isletter, content) && length(content) > 1
    print(io, "\\mathrm{$content}")
  else
    print(io, content)
  end
end

function show_latex_infix(io::IO, expr::GATExpr, op::String;
                          paren::Bool=false, kw...)
  show_latex_paren(io, expr) = show_latex(io, expr, paren=true)
  sep = op == " " ? op : " $op "
  if (paren) print(io, "\\left(") end
  join(io, [sprint(show_latex_paren, arg) for arg in args(expr)], sep)
  if (paren) print(io, "\\right)") end
end

function show_latex_postfix(io::IO, expr::GATExpr, op::String; kw...)
  @assert length(args(expr)) == 1
  print(io, "{")
  show_latex(io, first(expr), paren=true)
  print(io, "}")
  print(io, op)
end

function show_latex_script(io::IO, expr::GATExpr, head::String;
                           super::Bool=false, kw...)
  print(io, head, super ? "^" : "_", "{")
  join(io, [sprint(show_latex, arg) for arg in args(expr)], ",")
  print(io, "}")
end

end
