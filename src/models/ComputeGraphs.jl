module ComputeGraphs

using ...Syntax

struct Node
  name::Union{Symbol, Nothing} # only for debugging purposes
  term::Union{AlgTermId, Nothing} # some nodes aren't defined in terms of other nodes
end

struct ComputeGraph{Tup} <: AbstractComputeGraph{Tup}
  theory::GAT
  nodes::Vector{Node}
end

function getindex(cg::ComputeGraph, i::Id)
  cg.nodes[i.index]
end

function TheoryInterface.add_term!(cg::ComputeGraph, t::AlgTermId)::Id
  push!(cg.nodes, n)
  Id(length(cg.nodes))
end

function getindex(v::CGVar)
  v.cg[v.id]
end

end
