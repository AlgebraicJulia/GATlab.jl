module DataStructs 
export NestedMatrix, CombinatorialModel, CombinatorialModelMorphism, 
       NestedType, NestedTerm, CombinatorialModelC, is_natural, getsort,
       TermIterator, TypeIterator

using StructEquality

using ...Syntax
import ...Syntax: getvalue, AlgSort, argsof, headof, gettheory, getcontext
using ...Syntax.TheoryMaps: bind_localctx
using ...Models
using ...Stdlib
using ..TypeScopes: partition, repartition, repartition_idx

# Nested Matrices
#################
abstract type AbsNest{T} end # to resolve mutually-recursive structs.
 
"""
The shape of the nested matrices depends on the indices of the outer matrix, 
though the depth of the nested matrices are always the same. Furthermore the 
dimensionality is consistent for every level of depth.

- `T` is the type at the very end of the nesting, which we call a "leaf".
- `depth` parameter is used for runtime sanity check.

In principle, this data structure is independent of GATs, but in practice each 
NestedMatrix has an associated TypeScope which gives meaning to the indices.
See `ScopedNM`.
"""
@struct_hash_equal mutable struct NestedMatrix{T}
  data::Union{T, AbsNest{T}}
  const depth::Int

  """Create a leaf matrix"""
  NestedMatrix{T}(data::T) where T = new{T}(data, 0)

  """Non-leaf matrix. Caller must manually provide depth if `data` is empty"""
  function NestedMatrix{T}(data::AbsNest{T}; depth = nothing) where T
    depth = isnothing(depth) ? (first(data).depth + 1) : depth
    depths = (m -> m.depth).(getvalue(data)) # depths of all matrices one level below
    if all(==(depth - 1), depths)
      sizes = depth == 1 ? Int[] : size.(getvalue.(data))
      err = "Not all submatrices have the same dimensionality: $sizes"
      length(unique(length.(sizes))) <= 1 || error(err)
      new{T}(data, depth)
    else
      error("Bad depths $depths != $(depth - 1)")
    end
  end
end

const NM = NestedMatrix

@struct_hash_equal struct Nest{T} <: AbsNest{T}
  val::Array{NM{T}} # array of nested matrices
end

Base.size(n::Nest{T}) where T = size(getvalue(n))

Base.length(n::Nest{T}) where T = length(getvalue(n))

Base.iterate(n::Nest{T}) where T = iterate(getvalue(n))

Base.iterate(n::Nest{T}, i) where T = iterate(getvalue(n), i)

Base.first(n::Nest{T}) where T = first(getvalue(n))

Base.getindex(n::Nest{T}, i) where T = getindex(getvalue(n), i)

Base.setindex!(n::Nest{T}, i, k) where T = setindex!(getvalue(n), i, k)

Base.CartesianIndices(n::Nest{T}) where T = CartesianIndices(getvalue(n))

function getvalue(n::Nest{T})::Array{NM{T}} where T 
  n.val
end

Base.length(nm::NM)::Int = 
  (nm.depth == 0) ? 1 : sum(length.(getvalue(getvalue(nm))); init=0)

getvalue(nm::NM) = nm.data

const Idx = CartesianIndex

"""Access a submatrix (not necessarily a leaf) of a NestedMatrix"""
function Base.getindex(nm::NM{T}, idx::Vector{<:Idx})::NM{T} where T
  res = nm 
  for i in idx
    res = res.data[i]
  end
  res
end

function Base.setindex!(nm::NM{T}, data::NM{T}, idx::Vector{<:Idx}) where T 
  if isempty(idx)
    # TODO if this is not depth=0, need to delete all elems of array, then add
    nm.depth == data.depth == 0 || error("Bad depth")
    nm.data = data.data
  else
    init_indices..., last_index = idx
    nm[init_indices].data[last_index] = data
  end
end 

"""
Get a canonical NestedMatrix which just has the branching structure, ignoring 
the data on the leaves.
"""
shape(nm::NM)::NM{Nothing} = const_nm(nm, nothing)

""" Replace all leaves with a constant value. Optionally deepcopy that value """
function const_nm(nm::NM, v::T; copy=false, type=nothing) where T
  map_nm(_ -> (copy ? deepcopy : identity)(v), isnothing(type) ? T : type, nm)
end

"""
Map a function over the leaf values of a NestedMatrix, returning one of 
identical shape. This must be a unary function (operating on the leaf value) 
unless `index=true`, in which case it must accept an argument for the nesting 
index as well as the leaf value. 
"""
function map_nm(fun, ret_type::Type, nm::NM; index=false, curr=Idx[])
  if nm.depth == 0
    elem::ret_type = index ? fun(curr, nm.data) : fun(nm.data)
    NM{ret_type}(elem)
  else
    res = Array{NM{ret_type}}(undef, size(nm.data)...)
    for I in CartesianIndices(res)
      res[I] = map_nm(fun, ret_type, getvalue(nm.data)[I]; index, curr=[curr..., I])
    end
    NestedMatrix{ret_type}(Nest(res); depth=nm.depth)
  end
end

"""
Get all the leaves of a NestedMatrix along with their coordinate indices.

The iterator navigates the nested matrix with a state consisting of the current 
position in the indexing and a boolean representing whether we should move down 
(descend in depth, if true) or across (to the next index at the same depth, if
false). The algorithm is a depth-first search.
"""
function Base.iterate(nm::NestedMatrix{T}, state=(true => Idx[])) where T
  down, idxs = state
  curr = nm[idxs]
  if down
    if curr.depth == 0 
      return (idxs => curr.data, false => idxs)
    else
      next_inds = CartesianIndices(curr.data)
      if isempty(next_inds)
        iterate(nm, false => idxs)
      else
        iterate(nm, true => [idxs..., first(next_inds)])
      end
    end
  else 
    if isempty(idxs)  
      return nothing
    else
      prev_idxs = idxs[1 : end-1]
      prev = nm[prev_idxs]
      nxt = iterate(CartesianIndices(prev.data), last(idxs))
      if isnothing(nxt)
        iterate(nm, false => prev_idxs)
      else 
        return iterate(nm, true => [prev_idxs..., first(nxt)])
      end
    end
  end 
end

Base.sum(nm::NestedMatrix{<:Number}) = if nm.depth == 0 
  nm.data 
else 
  sum(getvalue.(nm.data)) # total sum of leaves
end

"""A NestedMatrix with a TypeScope to make sense of the indexing"""
@struct_hash_equal struct ScopedNM{T}
  val::NM{T}
  sort::AlgSort
  ts::TypeScope
  partition::Vector{Vector{LID}}
  function ScopedNM(val::NM{T}, theory::GAT, s::AlgSort) where T
    ts = getcontext(theory, s)
    new{T}(val, s, ts, partition(ts))
  end
  function ScopedNM(val::NM{T}, scope::TypeScope, s::AlgSort) where T
    new{T}(val, s, scope, partition(scope))
  end
end

getvalue(s::ScopedNM) = s.val
getsort(s::ScopedNM) = s.sort
getcontext(s::ScopedNM) = s.ts

shape(s::ScopedNM) = shape(getvalue(s))

Base.sum(s::ScopedNM) = sum(getvalue(s))

Base.length(s::ScopedNM{T}) where T = length(getvalue(s))

Base.iterate(s::ScopedNM{T}) where T = iterate(getvalue(s))

Base.iterate(s::ScopedNM{T}, i) where T = iterate(getvalue(s), i)

Base.getindex(n::ScopedNM{T}, i) where T = getindex(getvalue(n), i)

Base.setindex!(n::ScopedNM{T}, i, k) where T = setindex!(getvalue(n), i, k)

map_nm(fun, ret_type, n::ScopedNM; kw...) = 
  ScopedNM(map_nm(fun, ret_type, getvalue(n); kw...), getcontext(n), getsort(n))

const_nm(n::ScopedNM, v; copy=false) = 
  ScopedNM(const_nm(getvalue(n), v; copy), getcontext(n), getsort(n))

const AlgDict{T} = Dict{AlgSort, NM{T}}

@struct_hash_equal struct ScopedNMs{T}
  val::Dict{AlgSort, ScopedNM{T}}
end

function ScopedNMs(theory::GAT, xs::AlgDict{T}) where T 
  ScopedNMs{T}(Dict(k=>ScopedNM(v, theory, k) for (k,v) in pairs(xs)))
end

function ScopedNMs{T}() where T 
  ScopedNMs{T}(Dict{AlgSort, ScopedNM{T}}())
end

getvalue(s::ScopedNMs{T}) where T = s.val

Base.getindex(s::ScopedNMs{T}, i) where T = getvalue(s)[i]

Base.keys(s::ScopedNMs{T}) where T  = keys(getvalue(s))

Base.length(s::ScopedNMs{T}) where T = length(getvalue(s))

Base.setindex!(s::ScopedNMs{T}, i, k) where T = setindex!(getvalue(s), i, k)

Base.iterate(s::ScopedNMs{T}) where T = iterate(getvalue(s))

Base.iterate(s::ScopedNMs{T}, i) where T = iterate(getvalue(s), i)

Base.haskey(s::ScopedNMs{T}, k::AlgSort) where T = haskey(getvalue(s), k)

Base.get(s::ScopedNMs{T}, k, v) where T = get(getvalue(s), k, v)

Base.values(s::ScopedNMs{T}) where T = values(getvalue(s))

const NMI = NM{Int}

const NMVI = NM{Vector{Int}}

const NMIs = ScopedNMs{Int}

const NMVIs = ScopedNMs{Vector{Int}}

# Nested Types and Terms 
########################

abstract type Nested end

"""
Effectively picks out a dependent set from a typescope which has been 
partitioned into levels (by `partition`). E.g. Hom2[[2,3],[5,1]] means 
Hom2(Hom#5(Ob#2 => Ob#3), Hom#1(Ob#2 => Ob#3)).
"""
@struct_hash_equal struct NestedType <: Nested
  s::AlgSort
  val::Vector{Idx}
  lookup::Vector{Pair{Int,Int}} # cached mapping for linear indexing
  NestedType(s,v=Idx[]) = new(s,v,make_lookup(v))
end

NestedType(s, vs::Vector{Vector{Int}}) = NestedType(s, [Idx(v...) for v in vs])

"""How to interpret a list of lists as a flat list"""
function make_lookup(xs)::Vector{Pair{Int,Int}}
  res = Pair{Int,Int}[]
  for (i, x) in enumerate(xs)
    for j in 1:length(x.I)
      push!(res, i => j)
    end
  end
  res
end

getvalue(nestedtype::NestedType) = nestedtype.val

getsort(n::NestedType)::AlgSort = n.s # type inference fails if we extend AlgSort?!

Base.getindex(nm::NestedMatrix, idx::NestedType) = nm[getvalue(idx)]

Base.setindex!(nm::NestedMatrix, data::NestedMatrix, idx::NestedType) = 
  setindex!(nm, data, getvalue(idx))
  
function Base.getindex(typ::NestedType, i::Int)  
  (x, y) = typ.lookup[i]
  getvalue(typ)[x][y]
end

function Base.setindex!(typ::NestedType, idx::Int, i::Int) 
  (x, y) = typ.lookup[i]
  new_idx = [y == j ? idx : val for (j, val) in enumerate(getvalue(typ)[x].I)]
  getvalue(typ)[x] = CartesianIndex(new_idx...)
end

"""Picks out an *element* of a dependent set (which is now assumed to be 1:n)."""
@struct_hash_equal struct NestedTerm <: Nested
  val::Int
  args::NestedType
end

getvalue(nestedterm::NestedTerm) = nestedterm.val

argsof(nestedterm::NestedTerm)::NestedType = nestedterm.args

getsort(n::NestedTerm)::AlgSort = getsort(argsof(n))

Base.getindex(nm::NestedMatrix{Vector{T}}, idx::NestedTerm) where T = 
  getvalue(nm[argsof(idx)])[getvalue(idx)]

function Base.setindex!(nm::NM{Vector{T}}, data::T, idx::NestedTerm) where T
  getvalue(nm[argsof(idx)])[getvalue(idx)] = data
end

"""
Helper function for `subterms`.

Suppose we have indices corresponding to elements of a typescope, e.g. 
Hom#2[1,2,3,4] (representing the third Hom2 between Hom#3(Ob#1=>Ob#2) and 
Hom#4(Ob#1=>Ob#2)). We return [[], [], [1,2], [1,2] ]
"""
function sub_indices(theory::GAT, lc::TypeScope)::Vector{Vector{Int}}
  map(1:length(lc)) do i
    type = getvalue(lc[LID(i)])
    bound = bind_localctx(GATContext(theory, lc), type)
    map(getidents(getcontext(theory, AlgSort(type)))) do j
      if GATs.isvariable(bound[j])
        return bound[j].body.lid.val
      else 
        error("$j: non var $(bound[j]) ")
      end
    end
  end
end

"""
A nested term like Hom2[1,3,2,1]#3 (i.e. the third Hom2 between 
Hom#2(Ob#1=>Ob#3) and Hom#1(Ob#1=>Ob#3)) produces a vector [Ob[]#1, Ob[]#3, 
Hom[2,1]#2, Hom[2,1]#1]
"""
function subterms(theory::GAT, trm::Nested)::Vector{NestedTerm}
  typ = trm isa NestedTerm ? argsof(trm) : trm
  ctx = getcontext(theory, getsort(trm))
  sub_inds = sub_indices(theory, ctx)
  map(1:length(ctx)) do i
    arg_srt = AlgSort(getvalue(ctx[LID(i)]))
    arg_localctx = getcontext(theory, arg_srt)
    part_subs = repartition(arg_localctx, sub_inds[i])
    arg_typ = NestedType(arg_srt, map(part_subs) do subs 
      CartesianIndex([typ[x] for x in subs]...)
    end)
    NestedTerm(typ[i], arg_typ)
  end
end

"""
Enumerate a NestedMatrix, yielding expressions like `compose[1,2,3,1,4]`

This ignores the leaf values of the NestedMatrix.
"""
struct TypeIterator
  s::ScopedNM{Int}
end
Base.length(s::TypeIterator) = length(s.s)
Base.eltype(::Type{TypeIterator}) = NestedType
Base.iterate(s::TypeIterator) = iterate(s, Iterators.Stateful(s.s))
Base.iterate(s::TypeIterator, it) = 
  isempty(it) ? nothing : (NestedType(getsort(s.s), popfirst!(it)[1]), it)
  
"""
Enumerate a typecon matrix, yielding expressions like `Hom[1,2]#1`, `Hom[1,2]#2`
"""
struct TermIterator
  s::ScopedNM{Int}
end

Base.length(s::TermIterator) = sum(s.s)

Base.eltype(::Type{TermIterator}) = NestedTerm

Base.iterate(s::TermIterator) = 
  iterate(s, (Iterators.Stateful(s.s), nothing, Int[]))

function Base.iterate(s::TermIterator, state)
  (it, idx, queue) = state
  if isempty(queue)
    if isempty(it)
      nothing
    else 
      idx, val = popfirst!(it)
      iterate(s, (it, idx, collect(1:val)))
    end 
  else
    nxt = popfirst!(queue)
    NestedTerm(nxt, NestedType(getsort(s.s), idx)), (it, idx, queue)
  end
end


# Base.iterate(s::ScopedNM{T}, i) where T = iterate(getvalue(s), i)


# Models 
########

""" 
A cardinality for each (dependent) set and a family of functions for each term 
constructor.

One might be tempted to call this a GATset.
"""
@struct_hash_equal struct CombinatorialModel
  theory::GAT
  sets::NMIs
  funs::NMIs
  function CombinatorialModel(t, s=NMIs(), f=NMIs(); check=true)
    s, f = [sf isa NMIs ? sf : ScopedNMs(t, sf) for sf in [s,f]]
    if check 
      Set(keys(s)) == Set(sorts(t)) || error("Bad sort keys $s")
      Set(keys(f)) == Set(funsorts(t)) || error("Bad fun keys $s")
    end
    new(t, s, f)
  end
end
const Comb = CombinatorialModel
gettheory(c::Comb) = c.theory

Base.getindex(m::Comb, s::Symbol) = m[AlgSort(gettheory(m), s)]

Base.getindex(m::Comb, s::AlgSort) = if haskey(m.sets,s)
  m.sets[s]
elseif haskey(m.funs, s)
  m.funs[s]
else 
  throw(KeyError(s))
end

function Base.setindex!(m::Comb, n::NMI, s::AlgSort) 
  val = ScopedNM(n, m.theory, s)
  if haskey(m.sets,s)
    m.sets[s] = val
  elseif haskey(m.funs, s)
    m.funs[s] = val
  end
end

Base.getindex(m::Comb, t::NestedType) = m[getsort(t)][t]

Base.getindex(m::ScopedNMs, t::Nested) = m[getsort(t)][t]

function Base.setindex!(m::ScopedNMs, val, t::Nested)
  m[getsort(t)][t] = val
end

Base.setindex!(m::Comb, data::NMI, t::NestedType) =
  m.sets[getsort(t)][getvalue(t)] = data

function random_cardinalities end # defined in CModels 

"""
Make sure cardinalities are consistent with each other and that function values 
are defined (nonzero) and within bounds.
"""
function validate(c::Comb)
  T = gettheory(c)
  init = Dict{AlgSort, NMI}() #NMIs()
  for s in sorts(T)
    initdict = Dict{AlgSort, NMI}(k=>get(init, k, NMI(0)) for k in sorts(T) if k != s)
    r = random_cardinalities(T; init=initdict)[s] # generate a random one 
    shape(c.sets[s]) == shape(r) || return false
    init[s] = getvalue(c.sets[s])
  end
  for (funsort, vs) in c.funs
    for (e, v) in collect(vs)
      retterm = c(NestedType(funsort, e))
      max = getvalue(c.sets[getsort(retterm)][argsof(retterm)])
      0 < v ≤ max || return false
    end
  end
  true
end

"""Mapping for each TypeConstructor"""
@struct_hash_equal struct CombinatorialModelMorphism
  components::NMVIs
  dom::Comb 
  codom::Comb
  function CombinatorialModelMorphism(c, d, cd)
    c = c isa NMVIs ? c : ScopedNMs(gettheory(d), c)
    gettheory(d) == gettheory(cd) || error("Theory mismatch")
    new(c, d, cd)
  end
end

const Morphism = CombinatorialModelMorphism

Base.getindex(c::Morphism, k::AlgSort) = components(c)[k]
Base.getindex(c::Morphism, k::Symbol) = components(c)[AlgSort(gettheory(c), k)]

gettheory(c::Morphism) = gettheory(c.dom)

components(c::Morphism) = c.components

function (f::Morphism)(t::NestedType)::NestedType
  T, srt = gettheory(f), getsort(t)
  NestedType(srt, repartition_idx(T, srt, Int[getvalue.(f.(subterms(T, t)))...]))
end

function (f::Morphism)(t::NestedTerm)::NestedTerm
  NestedTerm(components(f)[getsort(t)][t], f(argsof(t)))
end

function is_natural(m::Morphism)
  T = gettheory(m)
  for (funsort, nestedmatrix) in m.dom.funs
    for (idx, _) in collect(nestedmatrix)
      # apply operation, then map over morphism
      dom_funapp = NestedType(funsort, idx)
      dom_funres = m.dom(dom_funapp)
      op_f = m(dom_funres)
      # map arguments to operation over morphism, then apply operation
      cod_idxs = getvalue.(m.(subterms(T, dom_funapp)))
      cod_funapp = NestedType(funsort, repartition_idx(T, funsort, cod_idxs))
      f_op = m.codom(cod_funapp)
      op_f == f_op || return false
    end
  end
  true
end

# Category instance 
###################

# For now, at least, the theory is run-time data.
@struct_hash_equal struct CombinatorialModelC <: Model{Tuple{Comb, Morphism}}
  theory::GAT
end

@instance ThCategory{Comb, Morphism} [model::CombinatorialModelC] begin
  function Ob(n::Comb) 
    model.theory == n.theory || @fail "Model theory mismatch"
    validate(n) ||  @fail "Failed validation"
    n
  end
  function Hom(f::Morphism, A::Comb, B::Comb)
    ThCategory.dom[model](f) == A ||  @fail "bad domain $A"
    ThCategory.codom[model](f) == B ||  @fail "bad codomain $B"
    is_natural(f) ||  @fail "unnatural"
    f
  end

  id(n::Comb) = Morphism(Dict(map(collect(n.sets)) do (k,v)
    k => map_nm(i->collect(1:i), Vector{Int}, getvalue(v))
  end), n, n)

  function compose(f::Morphism, g::Morphism) 
    Morphism(Dict(map(collect(components(f))) do (k, fk)
      b = f.codom
      g.dom == b || error("Cannot compose $f and $g")
      function fun(idx::Vector{<:Idx}, vs::Vector{Int})::Vector{Int}
        map(1:length(vs)) do i
          b_term = NestedTerm(i, NestedType(k, idx))
          components(g)[f(b_term)]
        end
      end
      k => map_nm(fun, Vector{Int}, getvalue(fk); index=true)
    end), f.dom, g.codom)
  end

  dom(A::Morphism) = A.dom
  codom(A::Morphism) = A.codom
end

end # module 
