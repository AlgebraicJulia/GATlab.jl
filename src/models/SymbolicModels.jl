module SymbolicModels
export GATExpr, @symbolic_model, SyntaxDomainError

using ...Syntax

using Base.Meta: ParseError
using MLStyle

abstract type GATExpr{T} end

"""
This module is for backwards compatibility with Catlab's @syntax macro.

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

struct SyntaxDomainError <: Exception
  constructor::Symbol
  args::Vector
end

function Base.showerror(io::IO, exc::SyntaxDomainError)
  print(io, "Domain error in term constructor $(exc.constructor)(")
  join(io, exc.args, ",")
  print(io, ")")
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
      $([Expr(:(::), nameof(binding), typename(theory, getvalue(binding))) for binding in termcon.args]...)
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
  Expr[symbolic_constructor(theoryname, x, getvalue(theory[x]), theory, parentmod) for x in termcons(theory)]
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
      $(structs...)

      $(accessors...)

      $(constructors...)
    end)
  )
end

end
