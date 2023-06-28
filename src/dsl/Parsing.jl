module Parsing

export Expr0, SurfaceExpr, CallExpr, InjectedTrm, RawVal, NewTerm, NewType,
  NewAxiom, Declaration, parse_decl, parse_surface, parse_bindings, gethead,
  getlines, parse_name

using ...Util

using MLStyle
using StructEquality
using ...Syntax

abstract type SurfaceExpr end

@struct_hash_equal struct CallExpr <: SurfaceExpr
  head::Name
  args::Vector{SurfaceExpr}
  function CallExpr(head::Name, args::Vector=SurfaceExpr[])
    new(head, args)
  end
end

gethead(e::CallExpr) = e.head

@struct_hash_equal struct InjectedTrm <: SurfaceExpr
  trm::Union{Trm, ATrm}
end

@struct_hash_equal struct RawVal <: SurfaceExpr
  val::Any
end

abstract type DeclBody end

struct NewTerm <: DeclBody
  head::Name
  args::Vector{Symbol}
  type::SurfaceExpr
end

@as_record NewTerm

struct NewType <: DeclBody
  head::Name
  args::Vector{Symbol}
end

@as_record NewType

struct NewAxiom <: DeclBody
  lhs::SurfaceExpr
  rhs::SurfaceExpr
  type::SurfaceExpr
  name::Name
end

@as_record NewAxiom

struct Declaration
  body::DeclBody
  context::Vector{Pair{Name, SurfaceExpr}}
end

const Expr0 = Union{Symbol, Expr}

function parse_name(e::Expr0)
  @match e begin
    (name::Symbol) => Name(name)
    :($(ann::QuoteNode)($(name::Symbol))) => Name(name; annotation=ann.value)
    _ => error("Could not parse $e as a name")
  end
end

function parse_args(e::Expr0)
  @match e begin
    (name::Symbol) => (Name(name), Any[])
    :($(name::Symbol)($(args...))) => (Name(name), Any[args...])
    :($(ann::QuoteNode)($(name::Symbol))) => (Name(name; annotation=ann.value), Any[])
    :($(ann::QuoteNode)($(name::Symbol))($(args...))) => (Name(name; annotation=ann.value), Any[args...])
    Expr(:block, _...) => begin
      lines = getlines(e)
      length(lines) == 1 || error("only one expression allowed in a block")
      parse_args(lines[1])
    end
    _ => error("Could not parse $e as an application of a head to arguments")
  end
end

parse_surface(x::Any) = RawVal(x)
parse_surface(e::Union{Trm, ATrm}) = InjectedTrm(e)

function parse_surface(e::Expr0)
  (name, args) = parse_args(e)
  CallExpr(name, parse_surface.(args))
end

function Base.show(io::IO, m::MIME"text/plain", e::CallExpr)
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

function normalize_decl(e)
  @match e begin
    :($name := $lhs == $rhs :: $typ ⊣ $ctx) => :(($name := ($lhs == $rhs :: $typ)) ⊣ $ctx)
    :($lhs == $rhs :: $typ ⊣ $ctx) => :(($lhs == $rhs :: $typ) ⊣ $ctx)
    :(($lhs == $rhs :: $typ) ⊣ $ctx) => :(($lhs == $rhs :: $typ) ⊣ $ctx)
    :($lhs == $rhs ⊣ $ctx) => :(($lhs == $rhs :: default) ⊣ $ctx)
    :($trmcon :: $typ ⊣ $ctx) => :(($trmcon :: $typ) ⊣ $ctx)
    :($trmcon ⊣ $ctx) => :(($trmcon :: default) ⊣ $ctx)
    e => e
  end
end

function parse_decl(e::Expr)
  @match normalize_decl(e) begin
    :($body ⊣ [$(bindings...)]) =>
      Declaration(
        parse_declbody(body),
        parse_bindings(bindings)
      )
    body => Declaration(parse_declbody(body), Pair{Symbol, SurfaceExpr}[])
    _ => error("Could not parse declaration $e")
  end
end

function parse_declbody(e::Expr0)
  @match e begin
    :($expr :: TYPE) => NewType(parse_args(expr)...)
    :($expr :: $type) => NewTerm(parse_args(expr)..., parse_surface(type))
    :($lhs == $rhs :: $type) =>
      NewAxiom(parse_surface(lhs), parse_surface(rhs), parse_surface(type), Anon())
    :($name := ($lhs == $rhs :: $type)) =>
      NewAxiom(parse_surface(lhs), parse_surface(rhs), parse_surface(type), Name(name))
    _ => error("Could not parse declaration head $e")
  end
end

function parse_bindings(bindings::AbstractVector)
  result = Pair{Name, SurfaceExpr}[]
  for binding in bindings
    @match binding begin
      :(($(heads...),)::$(type::Expr0)) => begin
        type_expr = parse_surface(type)
        append!(result, map(head -> parse_name(head) => type_expr, heads))
      end
      :($head::$(type::Expr0)) =>
        push!(result, parse_name(head) => parse_surface(type))
      :($head) =>
        push!(result, parse_name(head) => CallExpr(Name(:default)))
      _ => error("could not parse binding $binding")
    end
  end
  result
end

function getlines(e::Expr)
  @match e begin
    Expr(:block, lines...) => Vector{Any}(filter(line -> typeof(line) != LineNumberNode, lines))
    _ => error("expected a block, got: $e")
  end
end

end # module
