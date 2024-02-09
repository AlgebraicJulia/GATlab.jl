"""Helper functions to construct Combinatorial Models"""
module Constructor 
export create_graph, create_petri, create_category 

using Test
using GATlab
using GATlab.Combinatorial.DataStructs: NM, NMI, Nest
using GATlab.NonStdlib.NonStdTheories: ThPetri

# ThGraph
#########

T = ThGraph.Meta.theory;
os, hs = sorts(T)

function create_graph(v::Int, es::Vector{Tuple{Int,Int}}=Tuple{Int,Int}[])
  sets = Dict(os => NMI(v), hs => NMI(Nest(map(Iterators.product(1:v,1:v)) do ij
    NMI(count(==(ij), es))
  end)))
  CombinatorialModel(ThGraph.Meta.theory, sets)
end

# ThPetri 
#########

Ss, Ts, Is, Os = sorts(ThPetri.Meta.theory)

function create_petri(I::AbstractMatrix{Int}, O::AbstractMatrix{Int})
  S, T = size(I)
  size(I) == size(O) || error("Dimension mismatch: $I vs $O")
  sets = Dict(Ss => NMI(S), Ts => NMI(T), 
              Is => NMI(Nest(NMI.(I))), Os=>NMI(Nest(NMI.(O))))
  CombinatorialModel(ThPetri.Meta.theory, sets)
end

# ThCategory 
############

T = ThCategory.Meta.theory;
os, hs = sorts(T)
otc, htc = getvalue.(T[x] for x in methodof.(sorts(T)));
c, i = getvalue.(T[x] for x in last.(termcons(T)));
cs, is = [AlgSort(s...) for s in termcons(T)]

const Path = Vector{Symbol}
const Edges = Dict{Symbol,Pair{Symbol,Symbol}}

""" 
Category via generators and relations. E.g. commutative square cat would be 

vs = [:A,:B,:C,;D], es=(ab=(:a=>:b),bd=(:b=>:d),ac=(:a=>:c), cd=(:c=>:d))
eqs = [  [[:ab,:bd], [:ac,:cd]]  ]

No fancy equational reasoning takes place: equality of terms is determined by 
converting all subpaths found in the equations to their normal form (the first 
element of the list of equands).
"""
function create_category(vs::Set{Symbol}, es::Edges=Edges(),
                         eqs::Vector{Vector{Path}}=Vector{Path}[])
  N = length(vs)
  vord = sort(collect(vs))
  vind = Dict(v => findfirst(==(v), vord) for v in vs)
  rep = Dict{Path,Path}() # map subpaths to simpler ones
  for eq in eqs
    for pth in eq[2:end]
      rep[pth] = first(eq) # assume first one in list is the normal form
    end
  end

  # All the paths initially known (id and generators)
  path_map = map(Iterators.product(1:N,1:N)) do ij
    [(ij[1]==ij[2] ? [Symbol[]] : [])..., 
     [[k] for (k, (s, t)) in collect(es) if (vind[s], vind[t]) == ij]...]
  end

  # Iteratively compose morphisms
  queue = Tuple{Vector{Symbol},Vector{Symbol}}[([i],[j]) 
    for ((i,(_,tᵢ)), (j, (sⱼ,_))) in 
    Iterators.product(collect(es), collect(es)) if tᵢ == sⱼ]

  step = 0
  while !isempty(queue)
    (step += 1) < 1000 || error("Overflow")
    f, g = pop!(queue)
    d, cd = vind[es[first(f)][1]], vind[es[last(g)][2]]
    concat = normalize!(rep, [f; g])
    idx = findfirst(==(concat), path_map[d, cd])
    if isnothing(idx)
      push!(path_map[d, cd], concat)
      for i in 1:N 
        for morph in filter(!isempty, path_map[i, d])
          push!(queue,(morph, concat)) 
        end
        for morph in filter(!isempty, path_map[cd, i])
          push!(queue,(concat, morph)) 
        end
      end   
    end
  end

  # Data for compose
  cdata = NMI(Nest(map(Iterators.product(1:N,1:N,1:N)) do (i,j,k)
    NMI(Nest(Array{NMI}(
      map(Iterators.product(path_map[i,j],path_map[j,k])) do (f,g)
        idx = findfirst(==(normalize!(rep, [f;g])), path_map[i, k]) 
        NMI(something(idx))
      end)); depth=1)
  end))

  sets = Dict(os => NMI(N), hs => NMI(Nest(map(Iterators.product(1:N,1:N)) do ij
                                    NMI(length(path_map[ij...]))
                                  end)))
  funs = Dict(is => NMI(Nest(map(i -> NMI(1), 1:N))), 
              cs => cdata)
  CombinatorialModel(T, sets, funs)
end

create_category(vs::Vector{Symbol}, es, eqs=Vector{Path}[]) =
  create_category(Set(vs), es, eqs)

create_category(vs::Set{Symbol}, es::NamedTuple, eqs=Vector{Path}[]) = 
  create_category(vs, Edges(pairs(es)), eqs)


# Helper functions 
"""Find a subarray within an array (from StackOverflow)"""
function issubarray(needle::Vector{T}, haystack::Vector{T})::Union{Nothing,Int} where T
  getView(vec, i, len) = view(vec, i:i+len-1)
  ithview(i) = getView(haystack, i, length(needle))
  return findfirst(i -> ithview(i) == needle, 1:length(haystack)-length(needle)+1)
end

"""Replace a subarray with another subarray"""
function repl!(pat::Vector{T}, rep::Vector{T}, data::Vector{T})::Bool where T
  i = issubarray(pat, data)
  isnothing(i) && return false 
  for _ in 1:length(pat) 
    popat!(data, i)
  end
  for r in reverse(rep)
    insert!(data, i, r)
  end
  true
end

"""Apply replacements greedily until no more can be applied"""
function normalize!(d::Dict{Vector{T},Vector{T}}, data::Vector{T}) where T
  while !isempty(d)
    if !all([repl!(k,v,data) for (k,v) in d])
      break 
    end
  end
  data
end
z = [1,1,2,5,6,1,2,3]
@test normalize!(Dict([1,2]=>[500]), z) == [1,500,5,6,500,3]

end # module 