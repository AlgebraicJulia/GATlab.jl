module TypeScopes 

using ...Syntax

# Managing TypeScopes
#####################
"""
Factor a dependent typescope into pieces which are independent. These chunks 
become the different layers of the NestedMatrix. The groupings (though not ordering 
within the groupings) should be independent 
of the permutation of terms in the typescope.

In other parts of the code (such as `repartition`) it's convenient to 
assume that the values of the partition are strictly increasing, rather than 
some permutation. This is not true in general and will have to be revised, but
for now a runtime check at the end makes sure this assumption holds.
"""
function partition(t::TypeScope)::Vector{Vector{LID}}
  if length(t) == 0 return Vector{LID}[] end
  res = [[LID(1)]]
  for i in LID.(2:length(t))
    vs = vars(t, i)
    intersects = findlast([!isempty(s ∩ vs) for s in res])
    if isnothing(intersects)
      push!(res[1], i)
    elseif intersects == length(res)
      push!(res, [i])
    else 
      push!(res[intersects + 1], i)
    end
  end
  flat = getvalue.(Iterators.flatten(res))
  sort(flat) == flat || error("Assumption of monotonic increase violated")
  res 
end

"""Get all idents"""
vars(ts::TypeScope, t::AlgAST)::Set{LID} = vars(ts, t.body)
vars(ts::TypeScope, t::GATs.MethodApp)::Set{LID} = 
  union(Set{LID}(),vars.(Ref(ts), t.args)...)
vars(ts::TypeScope, t::Ident)::Set{LID} = 
  union(Set([t.lid]), vars(ts, getvalue(ts[t.lid])))
vars(ts::TypeScope, i::LID)::Set{LID} = vars(ts, getvalue(ts[i]))

function subscope(t::TypeScope, js::Vector{LID})::TypeScope
  d = Dict{LID,LID}([j=>LID(i) for (i, j) in enumerate(js)])
  TypeScope(Binding{AlgType}[relid(d, t[j]) for j in js]; tag=gettag(t))
end

subscope(t::TypeScope, i::LID)::TypeScope = 
  subscope(t, LID[sort(collect(vars(t, i)); by=getvalue); i])

relid(t::Dict{LID, LID}, x) = error("HERE $t $x $(typeof(x))") 
relid(t::Dict{LID, LID}, x::Binding) = setvalue(x, relid(t, getvalue(x))) 
relid(t::Dict{LID, LID}, x::T) where T<:AlgAST = T(relid(t, bodyof(x))) 
relid(t::Dict{LID, LID}, x::GATs.MethodApp{AlgTerm}) =
  GATs.MethodApp{AlgTerm}(headof(x),methodof(x),relid.(Ref(t),argsof(x))) 
relid(t::Dict{LID, LID}, x::Ident) = Ident(gettag(x), t[getlid(x)], nameof(x))


"""
Take a vector corresponding to idents of a typescope and group them together 
according to the partition
"""
repartition(ts::TypeScope, v) = repartition(length.(partition(ts)), v)

repartition_idx(t::GAT, s::AlgSort, v::Vector{Int}) = 
  [CartesianIndex(x...) for x in repartition(getcontext(t, s), v)]

""" lens = [3,3,2], v = [a,b,c,d,e,f,g,h] => [[a,b,c],[d,e,f],[g,h]] """
function repartition(lens::Vector{Int}, v::Vector{T})::Vector{Vector{T}} where T 
  cs = zip([0, lens...] .+ 1, cumsum(lens))
  [v[i:j] for (i,j) in cs] 
end
  
end # module