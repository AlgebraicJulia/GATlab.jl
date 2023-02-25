module Parse
export parse_symexpr, parse_declaration, add_decls, @theory

using ..GATs
using ..GATs: EmptyTheory, rename

using MLStyle
using StructEquality

@struct_hash_equal struct SymExpr
  head::Symbol
  args::Vector{SymExpr}
  function SymExpr(head::Symbol, args::Vector{SymExpr}=SymExpr[])
    new(head, args)
  end
end

abstract type DeclBody end

struct NewTerm <: DeclBody
  head::Symbol
  args::Vector{Symbol}
  type::SymExpr
end

@as_record NewTerm

struct NewType <: DeclBody
  head::Symbol
  args::Vector{Symbol}
end

@as_record NewType

struct NewAxiom <: DeclBody
  lhs::SymExpr
  rhs::SymExpr
  type::SymExpr
end

@as_record NewAxiom

struct Declaration
  body::DeclBody
  context::Vector{Pair{Symbol, SymExpr}}
end

const Expr0 = Union{Symbol, Expr}

function parse_args(e::Expr0)
  @match e begin
    (name::Symbol) => (name, Expr0[])
    :($(name::Symbol)($(args...))) => (name, Expr0[args...])
    _ => error("Could not parse $e as an application of a head to arguments")
  end
end

function parse_symexpr(e::Expr0)
  (name, args) = parse_args(e)
  SymExpr(name, parse_symexpr.(args))
end

function Base.show(io::IO, m::MIME"text/plain", e::SymExpr)
  print(io, string(e.head))
  if length(e.args) != 0
    print(io, "(")
    for arg in e.args[1:end-1]
      show(io, m, arg)
      print(io, ",")
    end
    show(io, m, e.args[end])
    print(io, ")")
  end
end

function parse_declbody(e::Expr0)
  @match e begin
    :($expr :: TYPE) => NewType(parse_args(expr)...)
    :($expr :: $type) => NewTerm(parse_args(expr)..., parse_symexpr(type))
    :($lhs == $rhs :: $type) => NewAxiom(parse_symexpr(lhs), parse_symexpr(rhs), parse_symexpr(type))
    _ => error("Could not parse declaration head $e")
  end
end

function parse_declaration(e::Expr)
  @match e begin
    :($body ⊣ [$(bindings...)]) =>
      Declaration(
        parse_declbody(body),
        parse_binding.(bindings)
      )
    _ => error("Could not parse declaration $e")
  end
end

function parse_binding(binding::Expr)
  @match binding begin
    :($(head::Symbol)::$(type::Expr0)) => (head => parse_symexpr(type))
    _ => error("could not parse binding $binding")
  end
end

function parse_judgement(context::Context, decl::Declaration)

end

"""
@theory ThSet <: Empty begin
  Ob::TYPE ⊣ []
end

@theory ThGraph <: ThSet begin
  Hom(x,y)::TYPE ⊣ [a::Ob, b::Ob]
end

@theory LawlessCategory <: Graph begin
  compose(f,g)::Hom(a,c) ⊣ [a::Ob, b::Ob, c::Ob, f::Hom(a,b), g::Hom(b,c)]
end
"""

end
