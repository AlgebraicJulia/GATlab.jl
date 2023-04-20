module ContextMaps
export interpret, interpret_term, show_context_map, KleisliContextMap

using ...StdTheories
using ....Syntax
using ....Models
using ....Util

module Impl

using .....Syntax
using .....Util

const Ob = Context

"""
Represents a Kleisli map in the monad for some theory

Each of the elements of `values` is a term in the context of `dom`.

This is the simplest implementation of a `ContextMap`, however it is not the
most efficient because it does not do deduplication of terms, so redundant
computations may be performed when interpreting.
"""
const Hom = AbstractVector{Trm}

"""
This assumes that `f` and `g` are valid context maps, and also
have compatible domain/codomain.
"""

"""
We assume that values is the values part of a KleisliContextMap `f`.

There are times when we have `values`, but we don't have the KleisliContextMap,
so it's worth exposing this method directly.

Assuming `t` is a term in the context `f.dom`, this produces a term in the
context `f.codom` by substituting each of the variables in `t` with the
corresponding term in `f.codom`.
"""
function substitute(t::Trm, f::Hom)
  if is_context(t.head)
    f[index(t.head)]
  else
    Trm(t.head, substitute.(t.args, Ref(f)))
  end
end

function compose(f::Hom, g::Hom)
  Trm[substitute(t, g) for t in f]
end

function compose(f::Hom, g::Hom, hs...)
  foldl([f, g, hs...]) do f′, g′
    compose(f′, g′)
  end
end

function id(ctx::Ob)
  Trm[Trm(Lvl(i; context=true)) for i in 1:length(ctx)]
end

function reindex(t::Trm, n::Int)
  if is_context(t.head)
    Trm(t.head + n, t.args)
  else
    Trm(t.head, reindex.(t.args, Ref(n)))
  end
end

function reindex(t::Typ, n::Int)
  Typ(t.head, reindex.(t.args, Ref(n)))
end

function mcompose(c1::Context, c2::Context)
  n = length(c1.ctx)
  Context(vcat(c1.ctx, Tuple{Name, Typ}[(name, reindex(t, n)) for (name,t) in c2.ctx]))
end

function mcompose(f::Hom, g::Hom, n::Int)
  vcat(f, reindex.(g, Ref(n)))
end

function codiag(c::Ob)
  vcat(id(c), id(c))
end

end

function interpret(m::Model, f::Impl.Hom, xs)
  [interpret_term.(Ref(m), f, Ref(xs))...]
end

function interpret_term(m::Model, t::Trm, xs)
  if is_context(t.head)
    xs[index(t.head)]
  else
    ap(m, Val(Int(index(t.head))), interpret_term.(Ref(m), t.args, Ref(xs))...)
  end
end

function show_context_map(io::IO, theory::Theory, dom::Context, codom::Context, f::Impl.Hom)
  for ((name,_), val) in zip(dom.ctx, f)
    print(io, string(name))
    print(io, " = ")
    println(io, show_term(theory, val, codom).judgment)
  end
end

struct KleisliContextMap <: TypedHom{Impl.Ob, Impl.Hom}
  dom::Impl.Ob
  codom::Impl.Ob
  morphism::Impl.Hom
  function KleisliContextMap(
    dom::Impl.Ob, codom::Impl.Ob,
    morphism::Impl.Hom
  )
    new(dom, codom, morphism)
  end
end

end
