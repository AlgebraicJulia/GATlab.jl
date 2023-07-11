module SymbolicModels

using ..Syntax

using Base.Meta: ParseError
using MLStyle

abstract type GATExpr end

"""
module FreeCategory
export Ob,Hom
using ..$__module__

theory() = ThCategory

struct Ob{T} <: ObExpr{T}
  args::Vector
  type_args::Vector{GATExpr}
end

struct Hom{T} <: HomExpr{T}
  args::Vector
  type_args::Vector{GATExpr}
end

function (::typeof(ThCategory.dom))(x::Hom)::Ob
  x.type_args[1]
end

function Ob(::Typ{Ob}, __value__::Any)::Ob
  Ob{:generator}([__value__], [])
end

function (::typeof(ThCategory.id))(A::Ob)::Hom
  Hom{:id}([A], [A, A])
end

end # module

function (::typeof(ThCategory.Hom))(x1::Any, x2::FreeCategory.Ob, x3::FreeCategory.Ob)::FreeCategory.Hom
  FreeCategory.Hom(x1, x2, x3)
end
"""


function typname(theory::Theory, typ::Typ)::Symbol
  Symbol(theory.judgments[typ.head].name)
end

function symbolic_struct(name, abstract_type)::Expr
  quote
    struct $name{T} <: $abstract_type{T}
      args::Vector
      type_args::Vector{$(GlobalRef(SymbolicModels, :GATExpr))}
    end
  end
end

function symbolic_structs(theory::Theory, abstract_types::Vector)::Vector{Expr}
  Expr[
    symbolic_struct(Symbol(j.name), abstract_type)
    for (j, abstract_type) in zip(typcons(theory), abstract_types)
  ]
end

function symbolic_typ_arg(theoryname, argname, typname, argtyp)
  quote
    function (::typeof($theoryname.$argname))(x::$typname)::$argtyp
      x.type_args[$arg_index]
    end
  end
end

function symbolic_typ_args(theory::Theory)::Vector{Expr}
  Expr[
    symbolic_typ_arg(theoryname, argname, Symbol(j.name), argtyp)
    for j in theory.judgments if j.head isa TypCon
      for (arg_index, (argname, argtyp)) in enumerate(j.ctx.ctx)
  ]
end

macro symbolic_model(decl, theoryname, body)
  theory = macroexpand(__module__, :($theoryname.@theory))
  (name, abstract_types) = @match decl begin
    Expr(:curly, name, abstract_types...) => (name, abstract_types)
    _ => throw(ParseError("Ill-formed head of @symbolic_model $decl"))
  end

  structs = symbolic_structs(theory, abstract_types)

  accessors = [
    for j in theory.judgments if j.head isa TypCon
      for (arg_index, (argname, argtyp)) in enumerate(j.ctx.ctx)
  ]

  constructors = [
    :(function (::typeof($theoryname.$(Symbol(j.name))))(
        $([Expr(:(::), Symbol(:x, i), $(typname(j.ctx[i][2]))) for (i, idx) in enumerate(j.head.args)])
      )

      end)
    for j in theory.judgments if j.head isa TrmCon
  ]
end

end
