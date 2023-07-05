module TheoryMaps
export TheoryIncl, TheoryMap, AbsTheoryMap, Composite

using ..Theories
using ..Theories: TrmTyp

using StructEquality

abstract type AbsTheoryMap end

dom(f::AbsTheoryMap) = f.dom
codom(f::AbsTheoryMap) = f.codom

@struct_hash_equal struct TheoryIncl <: AbsTheoryMap
    dom::Theory
    codom::Theory
    map::Vector{Int}
    function TheoryIncl(d,c,m) 
      # basic type checking ...
      length(m)==length(unique(m)) || error("TheoryIncl must be injective: $m")
      new(d,c,m)
    end 
end

const Composite = Union{Typ, Trm, Nothing}

@struct_hash_equal struct TheoryMap <: AbsTheoryMap
  dom::Theory
  codom::Theory
  composites::Vector{Composite}
  function TheoryMap(d, c, cs; partial=false)
    lc, ld = length.([cs, d])
    if !partial
      lc == ld || error("Bad composite length: $lc != $ld")
    end
    return new(d,c,cs)
  end
end

Base.getindex(t::TheoryMap, i::Integer) = t.composites[i]
Base.collect(t::TheoryMap) = collect(t.composites)
Base.length(t::TheoryMap) = length(t.composites)
(t::TheoryMap)(i::Integer) = t[i]

"""Map a context in the domain theory into a context of the codomain theory"""
(f::TheoryMap)(c::Context) =  Context([(a,f(b)) for (a,b) in c.ctx])

"""
Suppose dom(f) is [X,Y,Z,P,Q] and codom(f) is [XX,ϕ,ψ]
suppose we have a term: P(a,Q(b,c)) ⊢ a::X,b::Y,c::Z i.e. 4({1},5({2},{3}))

f maps all sorts to XX
f maps {P(x,y) ⊢ x::X,y::Y} to ϕ(ψ(y),x) i.e. 2(3({2}),{1})
and {Q(u,w) ⊢ u::Y,w::Z}    to ψ(w)      i.e. 3({2})

We should our term translate first to ϕ(ψ(y),x)  i.e.  2(3({2}),{1})

and then substitute x (i.e. {1}) for the mapped first argument 
y (i.e. 5) for f(q(b,c)) i.e. ϕ(ψ(ψ(c)),x) 2(3(3({3})),{1})

So f(4({1},5({2},{3}))) = 2(3(3({3})),{1})
"""
function (f::TheoryMap)(t::TrmTyp)  # e.g. P(a,q(b,c)) i.e. 4({1},5({2},{3}))
  if is_context(t.head) return t end  
  new_trm = f(index(t.head)) # e.g. ϕ(ψ(y),x) i.e. 2(3({2}),{1})
  n_args = f.(t.args) # [{1},3({3})] 
  old_j = f.dom[t.head]
  subs = Vector{Union{Nothing,Trm}}(fill(nothing, length(old_j.ctx)))
  for (i,a) in enumerate(old_j.head.args)
    subs[index(a)] = n_args[i]
  end
  return substitute(new_trm, subs)
end 

substitute(t::T, ts::Vector{Union{Nothing,Trm}}) where {T<:TrmTyp} = 
  is_context(t.head) ? ts[index(t.head)] : T(t.head, substitute.(t.args, Ref(ts)))

end # module
