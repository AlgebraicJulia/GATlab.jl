module Parsing

export Expr0, SymExpr, NewTerm, NewType, NewAxiom, Declaration, parse_decl, parse_symexpr, parse_binding, head

using ...Util

using MLStyle
using StructEquality

@struct_hash_equal struct SymExpr
  head::Symbol
  args::Vector{SymExpr}
  function SymExpr(head::Symbol, args::Vector=SymExpr[])
    new(head, args)
  end
end

head(e::SymExpr) = e.head

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
  name::Name
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

function reassociate_decl(e)
  @match e begin
    :($name := $lhs == $rhs :: $typ ⊣ $ctx) => :(($name := ($lhs == $rhs :: $typ)) ⊣ $ctx)
    :($lhs == $rhs :: $typ ⊣ $ctx) => :(($lhs == $rhs :: $typ) ⊣ $ctx)
    e => e
  end
end

function parse_decl(e::Expr)
  @match reassociate_decl(e) begin
    :($body ⊣ [$(bindings...)]) =>
      Declaration(
        parse_declbody(body),
        parse_binding.(bindings)
      )
    body => Declaration(parse_declbody(body), Pair{Symbol, SymExpr}[])
    _ => error("Could not parse declaration $e")
  end
end

function parse_declbody(e::Expr0)
  @match e begin
    :($expr :: TYPE) => NewType(parse_args(expr)...)
    :($expr :: $type) => NewTerm(parse_args(expr)..., parse_symexpr(type))
    :($lhs == $rhs :: $type) =>
      NewAxiom(parse_symexpr(lhs), parse_symexpr(rhs), parse_symexpr(type), Anon())
    :($name := ($lhs == $rhs :: $type)) =>
      NewAxiom(parse_symexpr(lhs), parse_symexpr(rhs), parse_symexpr(type), Name(name))
    _ => error("Could not parse declaration head $e")
  end
end

function parse_binding(binding::Expr)
  @match binding begin
    :($(head::Symbol)::$(type::Expr0)) => (head => parse_symexpr(type))
    _ => error("could not parse binding $binding")
  end
end

end
