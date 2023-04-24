module LensMacros
export @lens, @system

using MLStyle

using ....Syntax
using ....Util

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

function construct_arena(T::Type{<:AbstractTheory}, bar_expr::Expr)
  theory = gettheory(T)
  pos, dir = @match bar_expr begin
    :($pos | $dir) => construct_context.(Ref(theory.judgments), (pos, dir))
  end
  SimpleArena{T}(pos, dir)
end

function lens_impl(T::Type{<:AbstractTheory};
                   dom::Expr, codom::Expr, expose::Expr, update::Expr)
  dom, codom = construct_arena.(Ref(T), [dom, codom])
  construct_lens(T, dom, codom, expose, update)
end

function construct_lens(
  ::Type{T},
  dom::SimpleArena{T}, codom::SimpleArena{T},
  expose::Expr, update::Expr
) where {T<:AbstractTheory}
  theory = gettheory(T)
  expose = construct_context_map(theory, codom.pos, dom.pos, getlines(expose))
  update = construct_context_map(theory, dom.dir, ContextMaps.Impl.mcompose(dom.pos, codom.dir), getlines(update))
  SimpleKleisliLens{T}(
    dom,
    codom,
    expose,
    update
  )
end

macro system(theory, body)
  esc(Expr(:call, system_impl, theory, getlines(body)))
end

function system_impl(T::Type{<:AbstractTheory}, lines::Vector)
  theory = gettheory(T)
  state = nothing
  params = nothing
  body = Expr[]
  for line in lines
    @match line begin
      # the $_ matches the linenumbernode inserted in every macro expansion
      :(@state $_ $ctx) => (state = ctx)
      :(@params $_ $ctx) => (params = ctx)
      e => push!(body, e)
    end
  end
  state != nothing || error("state not provided to @system macro")
  params != nothing || error("params not provided to @system macro")
  dom_pos = construct_context(theory.judgments, state)
  dom_dir = Context(
    map(dom_pos.ctx) do (name, type)
      (Name(name; annotation=:d), type)
    end)
  codom_pos = dom_pos
  codom_dir = construct_context(theory.judgments, params)
  SimpleKleisliLens{T}(
    SimpleArena{T}(dom_pos, dom_dir),
    SimpleArena{T}(codom_pos, codom_dir),
    ContextMaps.Impl.id(dom_pos),
    construct_context_map(
      theory, dom_dir,
      ContextMaps.Impl.mcompose(dom_pos, codom_dir), body
    )
  )
end

end
