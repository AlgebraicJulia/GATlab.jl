export Pattern, compile

using ..EGraphs
using ...Syntax

using MLStyle

""" Pattern

A Pattern is an AlgTerm `trm` in a context `ctx`.

Patterns are compiled into programs that search for a morphism `f` from the
context into the e-graph such that `f(trm)` also exists in the e-graph.

TODO: enforce all terms in the context are used
"""
struct Pattern
  ctx::GATContext
  trm::AlgTerm
end

"""

- `v2r`: a map of variables to registers
- `free_vars`: indexed according to pattern vector of eterms, gives free variables
- `subtree_size`: indexed according to pattern vector of eterms, gives size of term
- `todo_nodes`: ???
- `instructions`: instructions which have been emitted so far
- `next_reg`: next free register
"""
struct CompileState
  v2r::Dict{Ident,Reg}
  free_vars::Vector{Set{Ident}}
  subtree_size::Vector{Int}
  todo_nodes::Dict{Tuple{Ident,Reg},ETerm}
  instructions::Vector{Instruction}
  next_reg::Reg
  theory::GAT
  function CompileState(theory::GAT)
    new(
      Dict{Ident,Reg}(),
      Set{Ident}[],
      Int[],
      Dict{Tuple{Int,Reg},ETerm}(),
      Instruction[],
      Reg(1),
      theory
    )
  end
end

"""
Takes a term, produces a vector of E-terms where the last e-term corresponds 
to the overall term. EIDs refer to indices within the vector. Returns the EID
of the overall term.

This is basically just a mini-egraph.
"""
function trm_to_vec!(trm::AlgTerm, vec::Vector{ETerm})
  ids = Vector{EId}(trm_to_vec!.(trm.args, Ref(vec)))
  push!(vec, ETerm(trm.head, ids))
  length(vec)
end

"""Inverse to trm_to_vec"""
function vec_to_trm(vec::Vector{ETerm}, id::EId)
  etrm = vec[id]
  args = Vector{AlgTerm}(vec_to_term.(Ref(vec), etrm.args))
  AlgTerm(etrm.head, args)
end

"""
Computes the set of free variables for each term, and the size of the subtree for each term.
"""
function load_pattern!(c::CompileState, patvec::Vector{ETerm})
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

function add_todo!(c::CompileState, patvec::Vector{ETerm}, id::EId, reg::Reg)
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
function next!(c::CompileState)
  function key(idreg::Tuple{EId,Reg})
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
  (k, v)
end

is_ground_now(c::CompileState, id::EId) = all(v ∈ keys(c.v2r) for v in c.free_vars[id])

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

  c = CompileState(mod.Meta.theory)

  load_pattern!(c, patvec)

  next_out = c.next_reg

  add_todo!(c, patvec, length(patvec), next_out)

  while true
    @match next!(c) begin
      nothing => break
      # I think etrm = patvec[id]?
      ((id, reg), etrm) => begin
        # If we've already bound all of the free variables of patvec[id]
        # then we can just lookup what patvec[id] should be
        if is_ground_now(c, id) && (length(etrm.args) != 0)
          extracted = extract(patvec, id)
          push!(
            c.instructions,
            Lookup(
              Union{ETerm,Reg}[is_context(t.head) ? c.v2r[t.head] : t for t in extracted],
              reg
            )
          )
        else
          out = next_out
          next_out += length(etrm.args)
          # Loop through all e-terms with head etrm.head
          # put their id in reg,
          # and their arguments in `out+1:out+length(etrm.args)`
          push!(
            c.instructions,
            Bind(
              etrm.head,
              reg,
              out + 1
            )
          )
          for (i, child) in enumerate(etrm.args)
            # Note that this only actually adds the todo if the argument is a
            # composite term not if the argument is an identifier
            add_todo!(c, patvec, child, out + i)
          end
        end
      end
    end
  end

  Program(
    c.instructions,
    Reg[r for (v, r) in sort([c.v2r...]; by=vr -> index(vr[1]))]
  )
end