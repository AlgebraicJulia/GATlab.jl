module Pushouts 
export pushout 

using ..Theories, ..TheoryMaps, ...Util
using ..Theories: TrmTyp
using DataStructures: IntDisjointSets, union!, find_root!


"""
v is a FinFunction from old de bruijn levels to new ones. Its domain is the 
size of the theory of the judgment.
"""
substitute_level(j::Judgment, v::Vector{Int}) =
  Judgment(j.name, substitute_level(j.head, v), substitute_level(j.ctx,v))
substitute_level(t::TrmCon, v::Vector{Int}) =
  TrmCon(t.args, substitute_level(t.typ, v)) 
substitute_level(t::TypCon, v::Vector{Int}) =
  TypCon(t.args, Ref(v)) 
substitute_level(t::Axiom, v::Vector{Int}) =
  Axiom(substitute_level(t.typ, v), substitute_level.(t.equands, Ref(v))) 
substitute_level(t::T, v::Vector{Int}) where {T<:TrmTyp} =
  T(is_context(t.head) ? t.head : Lvl(v[index(t.head)]), 
    substitute_level.(t.args, Ref(v)))
substitute_level(ctx::Context, v::Vector{Int}) =
  Context([(n,substitute_level(l, v)) for (n,l) in collect(ctx)])



"""
Pushout two inclusions. 
    f
  A ↪ B 
g ↓   ↓
  C->⌜D

D is thought of as a copy of B with the unmerged judgments of C added aftewards.
 
"""
function pushout(new_name::Name, f::TheoryIncl, g::TheoryIncl;  
                 rename_b::Dict{Int,Name}=Dict{Int,Name}(), 
                 rename_c::Dict{Int,Name}=Dict{Int,Name}())
  dom(f) == dom(g) || error("Domains must match")
  B,C = codom(f), codom(g)
  nB, nC = length.(judgments.([B,C]))
  hit = Union{Int,Nothing}[nothing for _ in 1:nC]
  for (i,j) in enumerate(f.map)
    hit[j] = i
  end
  CmA = Int[j for j in 1:nC if isnothing(hit[j])]
  next = nB
  CtoD = map(1:nC) do j
    if !isnothing(hit[j])
      f.map[hit[j]]
    else
      next += 1
    end
  end
  D = Theory(
    new_name,
    vcat(
      map(enumerate(B.judgments)) do (i, jmt)
        name = get(rename_b, i, jmt.name)
        rename(jmt, name)
      end,
      map(CmA) do j
        jmt = C.judgments[j]
        name = get(rename_c, j, jmt.name)
        substitute_level(rename(jmt, name), CtoD)
      end
    )
  )
  return (D, TheoryIncl(B,D,collect(1:nB)), TheoryIncl(C,D,CtoD))
end



end # module
