module SymbolicModels
export GATExpr, @symbolic_model

using ...Syntax

using Base.Meta: ParseError
using MLStyle

abstract type GATExpr{T} end

"""
module FreeCategory
export Ob,Hom
using ..__module__

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


function typname(theory::Theory, typ::Typ)
  Symbol(theory[typ.head].name)
end

function symbolic_struct(name, abstract_type, parentmod)::Expr
  quote
    struct $(esc(name)){T} <: $parentmod.$(abstract_type){T}
      args::$(Vector)
      type_args::$(Vector){$(GlobalRef(SymbolicModels, :GATExpr))}
    end
  end
end

function symbolic_structs(theory::Theory, abstract_types, parentmod)::Vector{Expr}
  Expr[
    symbolic_struct(Symbol(j.name), abstract_type, parentmod)
    for (j, abstract_type) in zip(typcons(theory), abstract_types)
  ]
end

function symbolic_accessor(theoryname, argname, typname, rettypname, argindex, parentmod)
  quote
    function (::$(typeof)($parentmod.$theoryname.$(Symbol(argname))))(x::$(esc(typname)))::$(esc(rettypname))
      x.type_args[$argindex]
    end
  end
end

function symbolic_accessors(theoryname, theory::Theory, parentmod)::Vector{Expr}
  Expr[
    symbolic_accessor(theoryname, argname, Symbol(j.name), typname(theory, argtyp), argindex, parentmod)
    for j in typcons(theory) for (argindex, (argname, argtyp)) in enumerate(j.ctx.ctx)
  ]
end

function symbolic_constructor(theoryname, j, theory, parentmod)
  quote
    function (::$(typeof)($parentmod.$theoryname.$(Symbol(j.name))))(
      $([Expr(:(::), Symbol(:x, i), esc(typname(theory, j.ctx[idx][2]))) for (i, idx) in enumerate(j.head.args)]...)
    )
      $(esc(typname(theory, j.head.typ))){$(Expr(:quote, Symbol(j.name)))}(
        $(Expr(:vect, [Symbol(:x, i) for i in 1:length(j.head.args)]...)),
        $(Vector){$(GlobalRef(SymbolicModels, :GATExpr))}()
      )
    end
  end
end

function symbolic_constructors(theoryname, theory::Theory, parentmod)::Vector{Expr}
  Expr[symbolic_constructor(theoryname, judgment, theory, parentmod) for judgment in trmcons(theory)]
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
