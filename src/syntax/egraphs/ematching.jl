# EMatching is the hard part of EGraphs
#
# Here we follow a strategy similar to egg, but modified somewhat for our uses.
#
# We take a pattern, which is a AlgTerm in a TypeScope, and we attempt to find an
# assignment of an enode to each variable in the scope.
#
# For instance, we might look for the term `(a * b) * c` in the context
# `[a,b,c::U]` or for the term `f ∘ id(a)` in the context
# `[a,b::Ob,f::Hom(a,b)]`.
#
# Note that not all variables in the context are referenced directly in the
# term; i.e. `b` is never referenced. Thus, ematching must take into account both
# terms and types.
export Reg, Scan, Bind, Compare, Lookup, Machine, run!,
  Pattern

using ..EGraphs
using ...Syntax

using MLStyle

struct Reg
  idx::Int
end

@as_record Reg

Base.:+(r::Reg, i::Int) = Reg(r.idx + i)

struct Machine
  reg::Vector{EId}
  lookup::Vector{EId}
  matches::Vector{Vector{EId}}
  limit::Union{Some{Int}, Nothing}
  function Machine(;limit=nothing)
    new(EId[], EId[], Vector{EId}[], limit)
  end
end

Base.getindex(m::Machine, r::Reg) = m.reg[r.idx]

Base.setindex!(m::Machine, r::Reg, i::EId) = (m.reg[r.idx] = i)

struct FinishedMatching <: Exception
end

function submit_match!(m::Machine, subst::Vector{Reg})
  match = EId[m[r] for r in subst]
  push!(m.matches, match)
  if !isnothing(m.limit) && length(m.matches) >= m.limit.value
    throw(FinishedMatching())
  end
end

@data Instruction begin
  # Iterate through all of the terms in the eclass bound to `i` that have term
  # constructor `trmcon`.
  #
  # For each term, assign the registers past `out` to the arguments of that term,
  # and run the rest of the instructions.
  Bind(trmcon::Ident, i::Reg, out::Reg)

  # Check if the eclass bound to `i` is the same as the eclass bound to `j`
  Compare(i::Reg, j::Reg)

  # Each element of `term` is either a register or an ETerm where the ids
  # refer to earlier elements of `term`. Fill out a lookup vector of ids the same
  # length as `term` by:
  # - For each Reg, just look up the id in the EGraph
  # - For each MethodApp, look up its arguments in the lookup vector (the arguments
  # to the MethodApp are indices into the lookup vector, not eids), and then look up
  # the completed ETerm in the EGraph
  #
  # At the end, put the last id in the lookup vector into `reg`.
  Lookup(term::Vector{Union{Reg, MethodApp{EId}}}, reg::Reg)

  # Iterate through every eclass in the egraph.
  #
  # For each eclass, assign its id to `out`, truncate the list of registers,
  # and run the rest of the instructions.
  #
  # Note: we can probably get better performance by only iterating through eclasses
  # with a certain ETyp.
  Scan(out::Reg)
end

struct Program
  instructions::Vector{Instruction}
  subst::Vector{Reg}
end

run!(m::Machine, eg::EGraph, prog::Program) = run!(m, eg, prog.instructions, prog.subst)

function run!(m::Machine, eg::EGraph, instructions::AbstractVector{Instruction}, subst::Vector{Reg})
  for idx in eachindex(instructions)
    @match instructions[idx] begin
      Bind(trmcon, i, out) => begin
        eclass = eg.eclasses[find!(eg, m[i])]
        remaining = @view instructions[idx+1:end]
        for etrm in eclass.reps
          if !(etrm.body isa MethodApp && etrm.body.method == trmcon)
            continue
          end
          resize!(m.reg, out.idx - 1)
          append!(m.reg, etrm.body.args)
          run!(m, eg, remaining, subst)
        end
        return
      end
      Compare(i, j) => begin
        if find!(eg, m[i]) != find!(eg, m[j])
          return
        end
      end
      Lookup(term, reg) => begin
        empty!(m.lookup)
        for x in trm
          @match x begin
            Reg(_) => push!(m.lookup, find!(eg, m[x]))
            MethodApp(decl, method, args) => begin
              etrm = ETerm(MethodApp(decl, method, EId[m.lookup[i] for i in args]))
              @match get(eg.hashcons, etrm, nothing) begin
                nothing => return
                id => push!(m.lookup, id)
              end
            end
          end
        end
        lookup[end] = find!(eg, m[reg])
      end
      Scan(out) => begin
        remaining = @view instructions[idx+1:end]
        for (id, eclass) in eg.eclasses
          resize!(m.reg, out.idx - 1)
          push!(m.reg, id)
          run!(m, eg, remaining, subst)
        end
        return
      end
    end
  end
  submit_match!(m, subst)
end

struct Compiler
  v2r::Dict{Ident, Reg}
  free_vars::Vector{Set{Ident}}
  subtree_size::Vector{Int}
  todo_nodes::Dict{Tuple{Ident, Reg}, ETerm}
  instructions::Vector{Instruction}
  next_reg::Reg
  theory::GAT
  function Compiler(theory::GAT)
    new(
      Dict{Ident, Reg}(),
      Set{Ident}[],
      Int[],
      Dict{Tuple{Int, Reg}, ETerm}(),
      Instruction[],
      Reg(1),
      theory
    )
  end
end

struct Pattern
  ctx::GATContext
  trm::AlgTerm
end

function trm_to_vec!(trm::AlgTerm, vec::Vector{ETerm})
  ids = Vector{EId}(trm_to_vec!.(trm.args, Ref(vec)))
  push!(vec, ETerm(trm.head, ids))
  length(vec)
end

function vec_to_trm(vec::Vector{ETerm}, id::EId)
  etrm = vec[id]
  args = Vector{AlgTerm}(vec_to_term(Ref(vec), etrm.args))
  AlgTerm(etrm.head, args)
end

function load_pattern!(c::Compiler, patvec::Vector{ETerm})
  n = length(patvec)

  for etrm in patvec
    free = Set{Ident}()
    size = 0
    hd = etrm.head
    if is_context(hd)
      push!(free, hd)
    else
      size = 1
      for arg in etrm.args
        union!(free, c.free_vars[arg])
        size += c.subtree_size[arg]
      end
    end
    push!(c.free_vars, free)
    push!(c.subtree_size, size)
  end
end

function add_todo!(c::Compiler, patvec::Vector{ETerm}, id::EId, reg::Reg)
  etrm = patvec[id]
  hd = etrm.head
  if is_context(hd)
    @match get(c.v2r, hd, nothing) begin
      nothing => (c.v2r[hd] = reg)
      j => push!(c.instructions, Compare(reg, j))
    end
  else
    c.todo_nodes[(id, reg)] = etrm
  end
end

# return an element x of xs such that f(x) is maximal
function maxby(f, xs)
  if isempty(xs)
    return nothing
  end
  next = iterate(xs)
  maxfound, state = next
  maxval = f(maxfound)
  while true
    next = iterate(xs, state)
    if !isnothing(next)
      x, state = next
      fx = f(x)
      if fx > maxval
        maxfound, maxval = x, fx
      end
    else
      break
    end
  end
  maxfound
end

# We take the max todo according to this key
# - prefer zero free variables
# - prefer more free variables
# - prefer smaller
#
# Free variables here means variables that are
# free in the term that have not been bound yet
# in c.v2r
#
# Why? Idk, this is how it works in egg
function next!(c::Compiler)
  function key(idreg::Tuple{EId, Reg})
    id = idreg[1]
    n_bound = length(filter(v -> v in keys(c.v2r), c.free_vars[id]))
    n_free = length(c.free_vars[id]) - n_bound
    (n_free == 0, n_free, -c.subtree_size[id])
  end

  k = maxby(key, keys(c.todo_nodes))
  if isnothing(k)
    return nothing
  end
  v = c.todo_nodes[k]
  delete!(c.todo_nodes, k)
  (k,v)
end

is_ground_now(c::Compiler, id::EId) = all(v ∈ keys(c.v2r) for v in c.free_vars[id])

function extract(patvec::Vector{ETerm}, i::EId)
  trm = vec_to_trm(patvec, i)
  vec = ETerm[]
  trm_to_vec!(trm, vec)
  vec
end

# Returns a Program
function compile(mod::Module, pat::Pattern)
  patvec = ETerm[]
  trm_to_vec!(pat.trm, patvec)

  c = Compiler(mod.Meta.theory)

  load_pattern!(c, patvec)

  next_out = c.next_reg

  add_todo!(c, patvec, length(patvec), next_out)

  while true
    @match next!(c) begin
      nothing => break
      ((id, reg), etrm) => begin
        if is_ground_now(c, id) && (length(etrm.args) != 0)
          extracted = extract(patvec, id)
          push!(
            c.instructions,
            Lookup(
              Union{ETerm, Reg}[is_context(t.head) ? c.v2r[t.head] : t for t in extracted],
              reg
            )
          )
        else
          out = next_out
          next_out += length(etrm.args)
          push!(
            c.instructions,
            Bind(
              etrm.head,
              reg,
              out + 1
            )
          )
          for (i, child) in enumerate(etrm.args)
            add_todo!(c, patvec, child, out + i)
          end
        end
      end
    end
  end

  Program(
    c.instructions,
    Reg[r for (v,r) in sort([c.v2r...]; by=vr -> index(vr[1]))]
  )
end
