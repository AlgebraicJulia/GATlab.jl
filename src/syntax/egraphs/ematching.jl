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
export Reg, Scan, Bind, Compare, Lookup, Machine, run!

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

