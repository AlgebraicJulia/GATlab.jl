"""
In this module, we provide facilities to extract a program for computing the
value of terms in an e-graph.

This takes advantage of variable-sharing in the e-graph, and minimizes number of
operations used.
"""
module ProgramExtraction

using ..EGraphs
using ...Syntax

using MLStyle
using JuMP

@data ComputeRef begin
  Argument(Int)
  Step(Int)
end

"""
A step of computation.

The context gives the indices of previous computation steps where the arguments
to the head were computed.
"""
struct ComputeStep
  head::Lvl
  context::Vector{ComputeRef}
end

struct AbstractComputeStep
  head::Lvl
  id::Id
  context::Vector{Id}
end

"""
A program in SSA form.
"""
struct Program
  steps::Vector{ComputeStep}
  out::Vector{ComputeRef}
end

abstract type ExtractionStrategy end

struct ILPExtract <: ExtractionStrategy
end

function extract_program(::ILPExtract, eg::EGraph, goal::Vector{Id})::Program
  # Step 1: Find the ETrms that we will use to compute the goal terms
  abstract_steps = select_etrms(eg, )
  # Step 2: Topologically sort them in order to schedule them

  # Step 3: Produce a Program by replacing e-class ids with step ids

end

function select_etrms(eg::EGraph, goal::Vector{Id})::Set{AbstractComputeStep}
  # Step 1: Compute contexts for each Etrm in `eg`

  # Step 2: Create a integer linear program whose solution is the optimal choice of etrms needed
  # to compute all of the eclass ids in `goal`, given values for the eclass ids in `start`

  # Step 3: Solve linear program, extract the relevant etrms into a set and return

end

end
