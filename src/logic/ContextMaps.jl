module ContextMaps
export ContextMap, KleisliContextMap

using ...Syntax

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
    Trm[substitute(t, g) for t in f.values]
  )
end

"""
Assuming `t` is a term in the context `f.dom`, this produces a term in the
context `f.codom` by substituting each of the variables in `t` with the
corresponding term in `f.codom`.
"""
function substitute(t::Trm, f::KleisliContextMap)
  if iscontext(t.head)
    f.values[index(t.head)]
  else
    Trm(t.head, substitute.(t.args, Ref(f)))
  end
end

function id(ctx::Context)
  KleisliContextMap(ctx, ctx, Trm[Trm(Lvl(i; context=true)) for i in 1:length(ctx)])
end

end
