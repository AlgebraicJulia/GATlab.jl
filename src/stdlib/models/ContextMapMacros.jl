module ContextMapMacros
export @context_map

using MLStyle

using ..ContextMaps
using ....Dsl.Parsing
using ....Dsl.TheoryMacros
using ....Dsl.TheoryMacros: term_impl, construct_context
using ....Syntax
using ....Logic
using ....Models
using ....Util

"""
Usage:

@context_map ThCategory [x::Ob, y::Ob, f::Hom(x,y)] [x::Ob, y::Ob, f::Hom(y,x)] begin
  x = y
  y = x
  f = f
end

(not supported yet)
@context_map ThGroup [x,y,z] [w] begin
  w = x * y * z * inv(x)
end

(not supported yet)
@context_map ThGroup [x,y,z] [out] begin
  out = x * y * z * inv(x)
end
"""
macro context_map(theory, dom, codom, body)
  dom = parse_ctx(dom)
  codom = parse_ctx(codom)
  esc(:(
    $(GlobalRef(ContextMapMacros, :context_map_impl))($theory.T, $dom, $codom, $(QuoteNode(body)))
  ))
end

function parse_ctx(expr::Expr0)
  @match expr begin
    (s::Symbol) => s
    Expr(:vect, vals...) => Expr0[vals...]
    _ => error("context must either be a name or a vector")
  end
end

function context_map_impl(
  T::Type{<:AbstractTheory},
  dom::Union{Context, Vector{Expr0}},
  codom::Union{Context, Vector{Expr0}},
  body::Expr
)
  theory = gettheory(T)
  dom = construct_context(theory, dom)
  codom = construct_context(theory, codom)
  lines = getlines(body)
  KleisliContextMap(
    dom,
    codom,
    construct_context_map(theory, dom, codom, lines)
  )
end

function construct_context_map(
  theory::Theory, dom::Context,
  codom::Context, lines::Vector
)
  values_by_name = Dict{Name, Trm}(parse_line(theory, codom, line) for line in lines)
  Trm[values_by_name[name] for (name,_) in dom.ctx]
end

function parse_line(T::Theory, ctx::Context, line)
  (name, value) = @match line begin
    Expr(:(=), name, value) => (parse_name(name), value)
    value => (Anon(), value)
  end
  (name, term_impl(T, value; context=ctx))
end

TheoryMacros.construct_context(theory::Theory, ctx::Context) = ctx
TheoryMacros.construct_context(theory::Theory, exprs::Vector{Expr0}) =
  construct_context(theory, parse_bindings(exprs))

end
