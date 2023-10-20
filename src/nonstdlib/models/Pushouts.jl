using DataStructures, StructEquality

export PushoutInt

using GATlab

"""Data required to specify a pushout. No fancy caching."""
@struct_hash_equal struct PushoutInt
  ob::Int
  i1::Vector{Int}
  i2::Vector{Int}
end

using .ThPushout 

@instance ThPushout{Int, Vector{Int}, PushoutInt} [model::FinSetC] begin
  @import Ob, Hom, id, compose, dom, codom
  function pushout(sp::Span; context)
    B, C = context[:d], context[:c]
    d = DataStructures.IntDisjointSets(B+C)
    [union!(d, sp.left[a], sp.right[a]+B) for a in 1:sp.apex]
    roots = DataStructures.find_root!.(Ref(d), 1:length(d))
    rootindex = sort(collect(Set(values(roots))))
    toindex = [findfirst(==(r),rootindex) for r in roots]
    PushoutInt(DataStructures.num_groups(d), 
     [toindex[roots[b]] for b in 1:B], 
     [toindex[roots[c+B]] for c in 1:C]
    )
  end
  cospan(p::PushoutInt) = Cospan(p.ob, p.i1, p.i2)
  function universal(p::PushoutInt, csp::Cospan; context)
    map(1:p.ob) do i
      for (proj, csp_map) in [(p.i1, csp.left), (p.i2, csp.right)]
        for (j, i′) in enumerate(proj)
          if i′ == i return csp_map[j] end
        end
      end
      error("Pushout is jointly surjective")
    end
  end
end
