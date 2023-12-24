"""Helpful functions for interacting with combinatorial models of GATs"""
module CModels

export interpret, add_part!, rem_part!

using ...Models
using ...Util.MetaUtils
using ...Syntax
import ...Syntax: GATContext, AlgSort, headof, argsof
using ...Syntax.TheoryMaps: infer_type, bind_localctx

using ..DataStructs 
using ..DataStructs: NMIs, NMI, getsort, subterms, ScopedNMs, ScopedNM, Nest
using ..TypeScopes: partition, subscope, vars, repartition, repartition_idx
import ..DataStructs: CombinatorialModel, random_cardinalities

# Generating random model
#########################

"""
Create a random combinatorial model, possibly with initialized data. For
unspecified cardinality data, a range of possible set sizes is specifiable.
"""
function CombinatorialModel(t::GAT; init=nothing, card_range=nothing)
  isets, ifuns = [Dict{AlgSort, NMI}() for _ in 1:2]
  for (k, v) in (isnothing(init) ? [] : init) 
    (k ∈ sorts(t) ? isets : ifuns)[k] = (v isa ScopedNM ? getvalue(v) : v)
  end
  sets = random_cardinalities(t, card_range; init=isets)
  funs = random_functions(sets, t; init=ifuns)
  CombinatorialModel(t, sets, funs)
end

"""
Randomly generate a choice of cardinality for every possible set associated 
with the sorts of a theory. This is a dependent process: the possible elements 
of |Ob| determine the possible elements of |Hom| (which happens to be |Ob|²).
But there can be trickiness depending on the signature, e.g.: 

Hom2(f,g) ⊣ [(a,b)::Ob, (f,g)::Hom(a,b)]  --- partition = [[1,2],[3,4]]

|Hom2| is NOT equal to |Hom|², since `f` and `g` are not completely independent:
they must have the same dom and codom. If we have:

  |Ob| = 2  |Hom(1,1)| = 2  |Hom(2,1)| = 0  |Hom(1,2)| = 1  |Hom(2,2)| = 1

e.g. Ob=[ω,β] Hom(ω,ω) = [η,μ] Hom(β,ω) = [] Hom(ω,β) = [δ] Hom(β,β) = [ξ]

Then we could potentially get a Hom2 matrix like:

       a=ω    a=β
    ⌜-------------⌝
b=ω | [3 2  |     |     i.e. Hom2(η,η) = |3|, Hom2(η,μ) = |2|, Hom2(μ,η) = |1|
    |  1 0] |[]₀ₓ₀|          Hom2(μ,μ) = |0|, Hom2(δ,δ) = |2|, Hom2(ξ,ξ) = |1|
    |-------------|
b=β |  [2]  | [1] |
    ⌞-------------⌟ 
"""
function random_cardinalities(theory::GAT, card_range=nothing;
                              init=nothing)::NMIs
  res = isnothing(init) ? NMIs() : (init isa Dict ? ScopedNMs(theory, init) : init)
  card_range = isnothing(card_range) ? (0:3) : card_range
  for sort in setdiff(sorts(theory), keys(res))
    ctx = getcontext(theory, sort)
    res[sort] = ScopedNM(rand_nm(res, theory, ctx, Int[], card_range), ctx, sort)
  end
  res
end

""" Generate random functions for a combinatorial model """
function random_functions(cards::NMIs, theory::GAT; init=nothing)::NMIs
  res = isnothing(init) ? NMIs() : (init isa Dict ? ScopedNMs(theory, init) : init)
  for s in funsorts(theory)
    haskey(res, s) && continue 
    res[s] = ScopedNM(random_function(cards, theory, s), theory, s)
  end
  res
end

""" 
Given a term constructor context, e.g. [(a,b,c)::Ob, f::a→b, g::b→c], and given 
some choices of sets (e.g. [[a=1,b=3,c=2],[f=2,g=4]]) determine the dependent set 
which is the codomain of the function and randomly pick an element of it.

"0" represents an unspecified output, which should be used if the codom is 
empty.
"""
function random_function(cards::NMIs, theory::GAT, s::AlgSort)
  tc = getvalue(theory[methodof(s)])
  lc = tc.localcontext
  retlc = getcontext(theory, AlgSort(tc.type))
  p = partition(retlc)
  function r(choices)
    sum(length.(choices)) == length(lc) || error(err)
    r = Dict(k.lid => v.body.lid for (k,v) in
              pairs(bind_localctx(GATContext(theory, lc), tc.type)))
    idxs = map(getidents(retlc)) do x
      r[x.lid].val # RELATE CHOICES OF TERMCON LC TO THAT OF TYPECON LC
    end
    card = index_nmi(getvalue(cards[AlgSort(tc.type)]), p, choices[idxs])
    card == 0 ? 0 : rand(1:card) # if codom is empty set, pick 0
  end
  rand_nm(cards, theory, lc, Int[], r, Int)
end


""" Random matrix for some typescope with uniform sampling of `vals`. """
function rand_nm(d::NMIs,t::GAT,lc::TypeScope, choices::Vector{Int}, 
                 vals::AbstractVector{T}) where T 
  rand_nm(d, t, lc, choices, (_)->rand(vals), T)
end

"""
Make a random NestedMatrix given the type scope for an AlgTypeConstructor.
`f` is a unary function of `choices` that returns a T
"""
function rand_nm(d::NMIs, theory::GAT, lc::TypeScope,  
                 choices::Vector{Int}, f::Function, T::Type)
  p = partition(lc)
  plens = [0, cumsum(length.(p))...]
  # Ranges of idxs in partition: e.g. p=[[1,2,4],[3,5],[7,6]] => [1:3,4:5,6:7]
  ranges = [UnitRange(a+1,b) for (a,b) in zip(plens, plens[2:end])]
  # Choices has decided values for some number of the partitions
  i = findfirst(==(length(choices)), plens)
  if i == length(p) + 1 # we have fully determined the whole context
    NMI(f(choices)) # pick an element to go in the leaf cell
  else 
    lens = map(LID.(ranges[i])) do idx 
      vs = sort(getvalue.(collect(vars(lc, idx))))
      idx_choices = choices[vs]
      Base.OneTo(length(enum(d, theory, subscope(lc,idx), idx_choices)))
    end
    NMI(Nest(Array{NestedMatrix{T}}(map(Iterators.product(lens...)) do idx
      rand_nm(d, theory, lc, [choices...,idx...], f, T)
    end)); depth = length(p) - i + 1)
  end
end

"""
Given a mapping of AlgSorts to cardinalities, e.g. (where we give arbitrary names)
Ob = [a,b]  Hom(1,1) = [c]  Hom(2,1) = []  Hom(1,2) = [d,e]  Hom(2,2) = [f,g]

Determine a cardinality in a context, e.g. |f| ⊣ [a::Ob, f::Hom(a,a)]

This example would result in: `[1, 1], [2, 1], [2, 2]` 
                        (i.e. `[a, c], [b, f], [b, g]`)
"""
function enum(cardinalities::NMIs, theory::GAT, ctx::TypeScope, init=Int[])
  queue = Vector{Int}[init]
  res = Vector{Int}[]
  while !isempty(queue)
    curr = popfirst!(queue)
    if length(curr) == length(ctx)
      push!(res, curr)
    else 
      typ = getvalue(ctx[LID(length(curr)+1)])
      s = AlgSort(typ)
      bound = bind_localctx(GATContext(theory, ctx), typ)
      rep = Dict(k.lid => v.body.lid for (k,v) in pairs(bound))
      p = Vector{Vector{LID}}(map(partition(getcontext(theory, s))) do seg
        LID[rep[x] for x in seg]  # need to reindex into ctx
      end)
      idx = index_nmi(getvalue(cardinalities[s]), p, curr)
      news = [[curr..., i] for i in 1:idx]
      append!(queue, news)
    end
  end
  res
end

"""
A NestedMatrix has been constructed with a particular type scope (and partition 
of the type scope) in mind. Given that partition (and choices of indices for each 
dimension), access an element of the NestedMatrix.
"""
function index_nmi(nmi::NestedMatrix{T}, p::Vector{Vector{LID}}, 
                   idx::Vector{Int}; depth::Int=0)::T where T
  depth+length(p) == nmi.depth || error("Bad indexing length $p vs $(nmi.depth)")
  for seg in p
    nmi = getvalue(getvalue(nmi))[idx[getvalue.(seg)]...]
  end
  nmi.depth == depth || error("Bad nmi $nmi") # sanity check
  getvalue(nmi)
end


# Modify cardinalities 
######################

"""
If we naively add a part to some set, there may be sets which
depend on the set which has been extended, so empty sets need to be created for 
all of these. E.g. if Ob=[1,2] and H11=[1], H12=[], H21=[1,2], H22[1].
If we add 3 to Ob, then we need to create H13=[], H31=[], H12=[], H32=[], H33=[].

Furthermore, new function arguments become possible, and the default value of 
the function is 0.

This implementation creates modified NestedMatrices and then replaces the ones 
in the CombinatorialModel. A more sophisticated algorithm would do this in place.
"""
function add_part!(m::CombinatorialModel, type::NestedType)::NestedTerm
  T = gettheory(m)
  enums = Dict(s => collect(m[s]) for s in sorts(T)) # store for later
  new_cardinality = getvalue(m[type]) + 1
  m[type] = NMI(new_cardinality)
  for s in sorts(T)
    getsort(type) ∈ sortsignature(getvalue(T, methodof(s))) || continue
    tc = getcontext(T, s)
    new_nm = rand_nm(m.sets, T, tc, Int[], [0]) # all empty sets
    for (e, val) in enums[s] # copy over old data
      new_nm[e] = NMI(val)
    end
    m[s] = new_nm
  end
  for s in funsorts(T)
    new_fun = random_function(m.sets, T, s)
    for (e, v) in m[s] # copy over old data
      new_fun[e] = NMI(v) 
    end
    m[s] = new_fun
  end
  NestedTerm(new_cardinality, type)
end

"""
Remove an element of a dependent set, specified by a NestedTerm. This has an 
effect on any sets dependent on that element. Removal involves pop-and-swap.

This implementation creates modified NestedMatrices and then replaces the ones 
in the CombinatorialModel. A more sophisticated algorithm would do this inplace.
"""
function rem_part!(m::CombinatorialModel, term::NestedTerm)
  T = gettheory(m)
  type = argsof(term)
  swapped_index = getvalue(m[type])
  m[type] = NMI(swapped_index - 1)
  for s in sorts(T)
    getsort(type) ∈ sortsignature(getvalue(T, methodof(s))) || continue
    new_nm = rand_nm(m.sets, T, getcontext(T, s), Int[], [0]) # all empty sets
    for e in TypeIterator(ScopedNM(new_nm, T, s))
      new_e = deepcopy(e)
      for (i, subterm) in enumerate(subterms(T, e))
        if subterm == term
          new_e[i] = swapped_index
        end
      end
      new_nm[e] = m[s][new_e]
    end
    m[s] = new_nm
  end
  for s in funsorts(T)
    new_fun = random_function(m.sets, T, s)
    for e in TypeIterator(ScopedNM(new_fun, T, s)) # copy over old data
      new_e = deepcopy(e)
      for (i, subterm) in enumerate(subterms(T, e))
        if subterm == term
          new_e[i] = swapped_index
        end
      end
      val = m(new_e)
      new_fun[e] = (val == term ? swapped_index : getvalue(val)) |> NMI
    end
    m[s] = new_fun
  end
end

"""
Convert a "NestedType" with a term constructor sort to an actual NestedTerm
by evaluating. E.g. compose[[1,4,5],[3,2]] => Hom[[1,5]]#4 via looking up in the 
compose table the value (4) and inferring the result type parameters.
""" 
function (m::CombinatorialModel)(term::NestedType)::NestedTerm
  T = gettheory(m)
  srt = getsort(term)
  rtype = getvalue(T[methodof(srt)]).type
  rsort = AlgSort(rtype)
  lc = bind_localctx(GATContext(T, getcontext(T, srt)), rtype)
  flat_idxs = map(sort(collect(pairs(lc)); by=x->getvalue(x[1].lid))) do (_,b)
    GATs.isvariable(b) ? term[getvalue(b.body.lid)] : error("Bad ret type $b")
  end
  idxs = repartition_idx(T, rsort, flat_idxs)
  NestedTerm(getvalue(m[term]), NestedType(rsort, idxs))
end

# Enforce equations
###################

"""Merely enforce equalities implied by equations of GAT via chase"""
function eq_saturate!(m::CombinatorialModel)
  error("NOT IMPLEMENTED YET") 
end

"""
Enforce equalities implied by equations of GAT via chase as well as create new 
elements of dependent sets for every undefined function output. This process 
can potentially not terminate.

Returns a boolean indicating whether or not the process terminated and an 
integer describing how many steps it took.
"""
function saturate!(m::CombinatorialModel; steps::Int=100)
  for step in 1:steps 
    eq_saturate!(m)
    error("NOT IMPLEMENTED YET")
    # ... && return (true, step) 
  end
  false, steps
end

is_saturated(m::CombinatorialModel) = last(saturate!(m)) == 0

end # module 
