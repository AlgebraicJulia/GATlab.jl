module HomSearch 
export homomorphism, homomorphisms

using StructEquality

using ..TypeScopes: partition, repartition
using ..DataStructs
using ..DataStructs: map_nm, sub_indices, subterms, getsort, Comb,
                     NM, NMI, NMIs, NMVI, NMVIs, const_nm, ScopedNMs
using ...Syntax
using ..Visualization
import ...Syntax: gettheory, argsof

""" Find a homomorphism between two attributed Combinatorial Models.

Returns `nothing` if no homomorphism exists. The
homomorphism problem is NP-complete and thus this procedure generally
runs in exponential time. It works best when the domain object is small.
"""
function homomorphism(X::Comb, Y::Comb; kw...)
  result = nothing
  backtracking_search(X, Y; kw...) do α
    result = α; return true
  end
  result
end

""" Find all homomorphisms between two attributed ``C``-sets.

This function is at least as expensive as [`homomorphism`](@ref) and when no
homomorphisms exist, it is exactly as expensive.
"""
function homomorphisms(X::Comb, Y::Comb; kw...) 
  results = CombinatorialModelMorphism[]
  backtracking_search(X, Y; kw...) do α
    push!(results, deepcopy(α)); return false
  end
  results
end

# Backtracking search
#--------------------
const Maybe{T} = Union{Nothing, T}

""" Internal state for backtracking search for CombinatorialModel homomorphisms.

Assignment of attribute variables maintains both the assignment as well as the 
number of times that variable has been bound. We can only *freely* assign the 
variable to match any AttrVar or concrete attribute value if it has not yet 
been bound.
"""
@struct_hash_equal struct BacktrackingState
  assignment::NMVIs
  assignment_depth::NMVIs
  inv_assignment::ScopedNMs{NMVI}
  refcounts::ScopedNMs{NMVI}
  unassigned::NMIs
  dom::Comb
  codom::Comb
end

gettheory(b::BacktrackingState) = b.dom.theory

function Base.show(io::IO, m::MIME"text/plain", s::BacktrackingState)
  for (k, v) in s.assignment
    println(io, k)
    show(io, m, v)
  end
end
Base.string(n::BacktrackingState) = sprint(show, MIME"text/plain"(), n)

"""
Allow opt-in constraints via `monic`/`epic`/`iso` kwargs. By default these are 
on the basis of each dependent set, so an iso constraint on Hom would mean that 
each Hom set is isomorphic to the hom set it is mapped to. Future work could 
include a constraint which could require domain ⨿Hom to be in bijection with 
codomain ⨿Hom. 

Future work is to allow finer granularity specification than the AlgSort level, 
e.g. Hom-Sets 1=>1 and 1=>2 are epic and Hom-Sets 2=>1 and 2=>2 are monic, etc.

Then `inv_assignment`s would have type NestedMatrix{Union{Nothing, Vector{Int}}}
"""
function normalize_monic_epic_iso(monic::Union{Bool, AbstractVector}, 
                                  epic::Union{Bool, AbstractVector}, 
                                  iso::Union{Bool, AbstractVector}, 
                                  theory::GAT
                                 )::Tuple{Vector{AlgSort},Vector{AlgSort}}
  Tsorts = sorts(theory)
  to_sort(s::Union{AlgSort, Symbol}) = s isa AlgSort ? s : AlgSort(theory, s)
  if iso == true
    return (Tsorts, Tsorts)
  else
    m, e = map([monic, epic]) do mono_epi 
      if mono_epi isa Bool 
        (mono_epi ? copy(Tsorts) : AlgSort[]) 
      else 
        to_sort.(mono_epi)
      end
    end
    if iso != false
      append!.([m,e], Ref(to_sort.(iso)))
    end
    (m, e)
  end
end

getinitial(::Comb, ::Comb, ::Nothing) = Pair{NestedTerm, NestedTerm}[]

"""An assignment (for each nonzero vector element) for all elements"""
function getinitial(X::Comb, Y::Comb, xys::NMVIs)
  m = CombinatorialModelMorphism(xys, X, Y)
  res = Pair{NestedTerm, NestedTerm}[]
  for s in sorts(gettheory(X))
    for (idx, vals) in get(xys, s, [])
      xtype = NestedType(s, idx)
      for xᵢ in 1:length(vals)
        x = NestedTerm(xᵢ, xtype)
        push!(res, x => m(x))
      end
    end
  end
  res
end

getinitial(::Comb, ::Comb, x::AbstractVector{Pair{NestedTerm, NestedTerm}}) = x

function backtracking_search(f, X::Comb, Y::Comb; monic=false, epic=false, 
                             iso=false, initial=nothing)
  X.theory == Y.theory || error("Theories must match for morphism search")
  T = X.theory
  
  monic, epic = normalize_monic_epic_iso(monic, epic, iso, T) 
  # TODO: constraint asserting a constraint across all elements of a sort
  # sort_monic, sort_epic = normalize_monic_epic_iso(monic′, epic′, iso′, T)  

  # Initialize state variables for search.
  assignment = NMVIs(Dict(c=>map_nm(i->zeros(Int,i), Vector{Int}, X.sets[c])   
                    for c in sorts(T)))
  assignment_depth = deepcopy(assignment)

  nmvis(c) =  const_nm(getvalue(X.sets[c]), map_nm(i->zeros(Int, i), Vector{Int}, 
                                                   getvalue(Y.sets[c])); copy=true)
  inv_assgn = ScopedNMs(T, Dict{AlgSort,NM{NMVI}}(c => nmvis(c) for c in monic))
  refcounts = ScopedNMs(T, Dict{AlgSort,NM{NMVI}}(c => nmvis(c) for c in epic))

  unassigned = NMIs(Dict(c => deepcopy(X.sets[c]) for c in epic))

  state = BacktrackingState(assignment, assignment_depth, inv_assgn, 
                            refcounts, unassigned, X, Y)

  # Make any initial assignments, failing immediately if inconsistent.
  for (x, y) in getinitial(X, Y, initial)
    assign_elem!(state, 0, x, y) || return false
  end
  # Start the main recursion for backtracking search.
  backtracking_search(f, state, 1)
end

function backtracking_search(f, state::BacktrackingState, depth::Int) 
  # Choose the next unassigned element.
  mrv, x = find_mrv_elem(state, depth)
  if isnothing(x)
    # No unassigned elements remain, so we have a complete assignment.
    return f(CombinatorialModelMorphism(state.assignment, state.dom, state.codom))
  elseif isempty(mrv)
    # An element has no allowable assignment, so we must backtrack.
    return false
  end

  # Iterate through all valid assignments of the chosen element.
  for y in mrv 
    @assert assign_elem!(state, depth, x, y) # find_mrv_elem checks assignment
    backtracking_search(f, state, depth + 1) && return true
    unassign_elem!(state, depth, x)
  end
  return false
end

""" Find an unassigned element having the minimum remaining values (MRV).
"""
function find_mrv_elem(state::BacktrackingState, depth::Int)
  T = gettheory(state)
  mrv, remaining_values, mrv_elem = Inf, NestedTerm[], nothing
  Y = state.codom
  for c in sorts(T), (depsₓ, depset) in state.assignment[c]
    for (xval, y) in enumerate(depset)
      y == 0 || continue
      x = NestedTerm(xval, NestedType(c, depsₓ))
      success = []
      for (depsᵧ, yvals) in Y.sets[c]
        for yval in 1:yvals 
          y = NestedTerm(yval, NestedType(c, depsᵧ))
          if can_assign_elem(state, depth, x, y)
            push!(success, y)
          end
        end
      end
      if length(success) < mrv
        mrv, remaining_values, mrv_elem = length(success), success, x
      end
    end
  end
  (remaining_values, mrv_elem)
end

""" Check whether element (c,x) can be assigned to (c,y) in current assignment.
"""
function can_assign_elem(state::BacktrackingState, depth::Int, x::NestedTerm, y::NestedTerm)
  # Although this method is nonmutating overall, we must temporarily mutate the
  # backtracking state, for several reasons. First, an assignment can be a
  # consistent at each individual subpart but not consistent for all subparts
  # simultaneously (consider trying to assign a self-loop to an edge with
  # distinct vertices). Moreover, in schemas with non-trivial endomorphisms, we
  # must keep track of which elements we have visited to avoid looping forever.
  save_state′ = deepcopy(state)
  ok = assign_elem!(state, depth, x, y)
  unassign_elem!(state, depth, x)
  for f in fieldnames(Comb)
    fa, fb = getfield.([save_state′.dom,state.dom], Ref(f))
    fa == fb || error("$f: \n$fa \n!= \n$fb")
  end
  save_state′ == state || error("Unassign x$(string(x))↦y$(string(y)) doesn't undo assign \n$(string(save_state′))\n\n$(string(state))")

  return ok
end

""" Attempt to assign element (c,x) to (c,y) in the current assignment.

Returns whether the assignment succeeded. Note that the backtracking state can
be mutated even when the assignment fails.
"""

function assign_elem!(state::BacktrackingState, depth::Int, x::NestedTerm, y::NestedTerm)
  c = getsort(x)
  c == getsort(y) || error("Mismatched sorts $c $(getsort(y))")
  y′ = state.assignment[x]
  sts = subterms(gettheory(state), x)
  ysts = [state.assignment[getsort(st)][st] for st in sts]
  ctx = getcontext(gettheory(state), c)
  yidxs = [CartesianIndex(i...) for i in repartition(ctx, ysts)]
  y′term = NestedTerm(y′, NestedType(c, yidxs))
  y′term == y && return true  # If x is already assigned to y, return immediately.
  y′ == 0 || return false # Otherwise, x must be unassigned.
  if haskey(state.inv_assignment, c) 
    if getvalue(state.inv_assignment[argsof(x)])[y] != 0
      return false # Also, y must unassigned in the inverse assignment.
    end
  end 
  # With an epic constraint, fail based on the # of unassigned in dom vs codom
  if haskey(state.refcounts, c)
    # Number of free values in x's set (X) we have remaining to fill y's set (Y)
    unassigned = getvalue(state.unassigned[argsof(x)])
    # How many elements of X are pointing at each element in Y 
    refcounts = getvalue(state.refcounts[argsof(x)])[argsof(y)] |> getvalue
    # How many elements of Y have nothing pointing at them from X.
    # (ignore y, as this value is about to be assigned to by x)
    to_assign = count(((i, rc),)-> i!=y′ && rc==0, enumerate(refcounts))
    if unassigned < to_assign
      return false
    end
  end
  # Set dependent set values based on type constructor arguments
  for (subX, subY) in zip(subterms.(Ref(gettheory(state)), [x,y])...)
    assign_elem!(state, depth, subX, subY) || return false
  end

  # Make the assignment and recursively assign subparts.
  state.assignment[x] = getvalue(y)
  state.assignment_depth[x] = depth
  if haskey(state.inv_assignment, c)
    inv = getvalue(state.inv_assignment[argsof(x)])
    inv[y] = getvalue(x)
  end
  if haskey(state.refcounts, c)
    xcounts = getvalue(state.refcounts[argsof(x)])
    xunassgn = state.unassigned[argsof(x)]
    xcounts[y] += 1
    xunassgn.data = xunassgn.data - 1
  end
  
  # Set other values based on term constructor naturality constraints
  for (funsort, fun_data) in state.dom.funs
    for (dom_deps, _) in fun_data  # check, for each combination of args:
      valX_expr = NestedType(funsort, dom_deps)
      valX = state.dom(valX_expr)
      sts = subterms(gettheory(state), valX_expr)
      any(==(x), sts) || continue # only if the term we just set is an arg
      ysts = [state.assignment[getsort(st)][st] for st in sts]
      any(==(0), ysts) && continue  # only if all args of this f(...) are defined
      yidxs = [CartesianIndex(i...) for i in repartition(length.(dom_deps), ysts)]
      valY = state.codom(NestedType(funsort, yidxs))
      assign_elem!(state, depth, valX, valY) || return false
    end
  end
  return true
end

function (state::BacktrackingState)(x::NestedTerm)
  sts = subterms(gettheory(state), x)
  (y, ysts...) = ys = [state.assignment[getsort(st)][st] for st in [x, sts...]]
  any(==(0), ys) && return nothing  # only if all args are defined
  lens = length.(partition(getcontext(gettheory(state), getsort(x))))
  yidxs = [CartesianIndex(i...) for i in repartition(lens, ysts)]
  NestedTerm(y, NestedType(getsort(x), yidxs))
end

""" Unassign the element (c,deps,x) in the current assignment.
"""
function unassign_elem!(state::BacktrackingState, depth::Int, x::NestedTerm)
  c = getsort(x)
  y = state(x)

  for sub in subterms(gettheory(state), x)
    unassign_elem!(state, depth, sub)
  end
  state.assignment[x] == 0 && return

  assign_depth = state.assignment_depth[x]
  @assert assign_depth <= depth
  assign_depth == depth || return 
  if haskey(state.inv_assignment, c)
    getvalue(state.inv_assignment[argsof(x)])[y] = 0
  end

  if haskey(state.unassigned, c)
    xcounts = getvalue(state.refcounts[argsof(x)])
    xunassgn = state.unassigned[argsof(x)]
    xcounts[y] -= 1
    xunassgn.data = xunassgn.data + 1
  end

  state.assignment[x] = 0
  state.assignment_depth[x] = 0

  for (funsort, fun_data) in state.dom.funs
    for (deps, _) in fun_data
      fx = NestedType(funsort, deps)
      if x ∈ subterms(gettheory(state), fx)
        fx_val = state.dom(fx)
        unassign_elem!(state, depth, fx_val)
      end
    end
  end
end

end # module 
