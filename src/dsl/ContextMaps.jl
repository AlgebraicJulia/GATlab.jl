module ContextMaps
export @context_map

using MLStyle
using ..Parsing
using ..TheoryMacros
using ..TheoryMacros: term_impl, construct_context
using ...Syntax
using ...Logic
using ...Models
using ...Util

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
@context_map ThGroup [x,y,z] [::U] begin
  x * y * z * inv(x)
end
"""
macro context_map(T, dom, codom, body)
  dom = parse_ctx(dom)
  codom = parse_ctx(codom)
  esc(:(
    $(GlobalRef(ContextMaps, :context_map_impl))($T, $dom, $codom, $(QuoteNode(body)))
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
  T = theory(T)
  dom = construct_context(T.judgments, dom)
  codom = construct_context(T.judgments, codom)
  body.head == :block ||
    error("expected a block to be passed in as the last argument to @context_map")
  lines = @match body begin
    Expr(:block, lines...) => filter(line -> typeof(line) != LineNumberNode, lines)
    _ => error("expected body of @context_map macro to be a block")
  end
  values_by_name = Dict{Name, Trm}(parse_line(T, codom, line) for line in lines)
  KleisliContextMap(
    dom,
    codom,
    Trm[values_by_name[name] for (name,_) in dom.ctx]
  )
end

function parse_line(T::Theory, ctx::Context, line)
  (name, value) = @match line begin
    Expr(:(=), name, value) => (Name(name), value) 
    value => (Anon(), value)
  end
  (name, term_impl(T, value; context=ctx))
end

TheoryMacros.construct_context(judgments::Vector{Judgment}, ctx::Context) = ctx
TheoryMacros.construct_context(judgments::Vector{Judgment}, exprs::Vector{Expr0}) =
  construct_context(judgments, parse_binding.(exprs))

end
