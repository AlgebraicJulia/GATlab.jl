module Petri
export lens_dynamics

using AlgebraicPetri
using Catlab.CategoricalAlgebra

using ..SimpleLenses
using ...StdTheories: ThRing
using ..ContextMaps
using ....Syntax
using ....Util
using ....Dsl

CtxTrm(i) = Trm(Lvl(i;context=true)) # upstream this?

function lens_dynamics(p::LabelledPetriNet, T::Type=ThRing)
  Th = gettheory(T)
  names = [p[:sname], [Symbol("d$s") for s in p[:sname]], p[:tname]]
  pos, dom_dir,codom_dir = map(names) do name 
    Context(Th, Name.(name))
  end
  dom = SimpleArena{T}(pos, dom_dir)
  codom = SimpleArena{T}(pos, codom_dir)
  expose = ContextMaps.Impl.id(pos)
  # Compute update, starting with each reaction rate
  rxn_rates = map(parts(p, :T)) do t
    tlvl = CtxTrm(t+nparts(p, :S))
    i = CtxTrm.(p[incident(p, t, :it),:is])
    sumterm = foldl((a,b)-> @term(T,$a * $b), i; init=@term(T, one))
    @term(T, $tlvl * $sumterm)
  end
  Zero = (init=@term(T, zero),)
  update = map(parts(p, :S)) do s 
    i, o = incident.(Ref(p), s, [:is, :os])
    sinks, srcs = map([rxn_rates[p[i,:it]], rxn_rates[p[o,:ot]]]) do rates 
      foldl((a,b)-> @term(T,$a + $b), rates; Zero...)
    end
    @term(T, $srcs + -$sinks)
  end
  SimpleKleisliLens{T}(dom,codom,expose,update)
end 

end # module
