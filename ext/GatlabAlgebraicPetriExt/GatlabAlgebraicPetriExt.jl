module GatlabAlgebraicPetriExt
export lens_dynamics

using AlgebraicPetri
using Catlab.CategoricalAlgebra

using Gatlab
import Gatlab: SimpleKleisliLens

CtxTrm(i) = Trm(Lvl(i;context=true)) # upstream this?

function SimpleKleisliLens(p::LabelledPetriNet, Th=ThRing)
  T = Th.T
  theory = gettheory(T)
  names = [p[:sname], [Symbol("d$s") for s in p[:sname]], p[:tname]]
  pos, dom_dir,codom_dir = map(names) do name 
    Context(theory, Name.(name))
  end
  dom = SimpleArena{T}(pos, dom_dir)
  codom = SimpleArena{T}(pos, codom_dir)
  expose = ContextMaps.Impl.id(pos)
  update_codom = ContextMaps.Impl.mcompose(pos, dom_dir)
  # Compute update, starting with each reaction rate
  rxn_rates = map(parts(p, :T)) do t
    tlvl = CtxTrm(t+nparts(p, :S))
    i = CtxTrm.(p[incident(p, t, :it),:is])
    sumterm = foldl((a,b)-> @term(Th, update_codom, $a * $b), i; init=@term(Th, one))
    @term(Th, update_codom, $tlvl * $sumterm)
  end
  Zero = (init=@term(Th, zero),)
  update = map(parts(p, :S)) do s 
    i, o = incident.(Ref(p), s, [:is, :os])
    sinks, srcs = map([rxn_rates[p[i,:it]], rxn_rates[p[o,:ot]]]) do rates 
      foldl((a,b)-> @term(Th, update_codom, $a + $b), rates; Zero...)
    end
    @term(Th, update_codom, $srcs + -$sinks)
  end
  SimpleKleisliLens{T}(dom,codom,expose,update)
end 

end # module
