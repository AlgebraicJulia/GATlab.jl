module LensMacros
export @lens

using MLStyle

using ....Syntax

using ....Dsl.Parsing
using ....Dsl.TheoryMacros: construct_context

using ..ContextMapMacros
using ..ContextMapMacros: construct_context_map
using ..ContextMaps
using ..SimpleLenses

macro lens(theory, body)
  function to_param(e::Expr0)
    @match e begin
      Expr(:(=), lhs, rhs) => Expr(:kw, lhs, QuoteNode(rhs))
      _ => error("expected an assignment, got $e instead")
    end
  end
  esc(Expr(:call, lens_impl, Expr(:parameters, to_param.(getlines(body))...), theory))
end

function lens_impl(T::Type{<:AbstractTheory}; dom::Expr, codom::Expr, expose::Expr, update::Expr)
  theory = gettheory(T)
  function make_arena(e::Expr)
    pos, dir = @match e begin
      :($pos | $dir) => construct_context.(Ref(theory.judgments), (pos, dir))
    end
    SimpleArena{T}(pos, dir)
  end
  dom, codom = make_arena.([dom, codom])
  expose = construct_context_map(theory, codom.pos, dom.pos, getlines(expose))
  update = construct_context_map(theory, dom.dir, ContextMaps.Impl.mcompose(dom.pos, codom.dir), getlines(update))
  SimpleKleisliLens{T}(
    dom,
    codom,
    expose,
    update
  )
end

end
