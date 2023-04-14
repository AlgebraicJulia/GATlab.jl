module ContextMaps
export ContextMap, KleisliContextMap, substitute, substitute_all, coproduct, coproduct_values, reindex, id_values

using ...Syntax
using ...Util

abstract type ContextMap end

"""
Represents a Kleisli map in the monad for some theory

Each of the elements of `values` is a term in the context of `dom`.

This is the simplest implementation of a `ContextMap`, however it is not the
most efficient because it does not do deduplication of terms, so redundant
computations may be performed when interpreting.
"""
struct KleisliContextMap <: ContextMap
  dom::Context
  codom::Context
  values::Vector{Trm}
end

"""
This assumes that `f` and `g` are valid context maps, and also
have compatible domain/codomain.
"""
function compose(f::KleisliContextMap, g::KleisliContextMap)
  KleisliContextMap(
    f.dom,
    g.codom,
    substitute_all(f.values, g.values)
  )
end

"""
We assume that values is the values part of a KleisliContextMap `f`.

There are times when we have `values`, but we don't have the KleisliContextMap,
so it's worth exposing this method directly.

Assuming `t` is a term in the context `f.dom`, this produces a term in the
context `f.codom` by substituting each of the variables in `t` with the
corresponding term in `f.codom`.
"""
function substitute(t::Trm, values::AbstractVector{Trm})
  if is_context(t.head)
    values[index(t.head)]
  else
    Trm(t.head, substitute.(t.args, Ref(values)))
  end
end

function substitute_all(ts::AbstractVector{Trm}, values::AbstractVector{Trm})
  Trm[substitute(t, values) for t in ts]
end

function substitute_all(fvals, gvals, hvalses...)
  foldl([fvals, gvals, hvalses...]) do ts, values
    substitute_all(ts, values)
  end
end

function id(ctx::Context)
  KleisliContextMap(ctx, ctx, id_values(ctx))
end

function id_values(ctx::Context)
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

function coproduct(c1::Context, c2::Context)
  n = length(c1.ctx)
  Context(vcat(c1.ctx, Tuple{Name, Typ}[(name, reindex(t, n)) for (name,t) in c2.ctx]))
end

function coproduct(f::KleisliContextMap, g::KleisliContextMap)
  KleisliContextMap(
    coproduct(f.dom, g.dom),
    coproduct(f.codom, g.codom),
    coproduct_values(f.values, g.values, length(f.codom))
  )
end

function coproduct_values(fvals::AbstractVector{Trm}, gvals::AbstractVector{Trm}, n::Int)
  vcat(fvals, reindex.(gvals, Ref(n)))
end

# function kleisli_coproduct(ts::AbstractVector{Trm}, ts′::AbstractVector{Trm})
#   vcat(ts, reindex(ts′, length(ts)))
# end

end
