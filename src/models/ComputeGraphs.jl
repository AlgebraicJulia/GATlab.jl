module ComputeGraphs
export ComputeGraph, Node, add_var!

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

function add_var!(cg::ComputeGraph, T)
  push!(cg.nodes, Node(nothing, nothing))
  TypedVar{T}(Id(length(cg.nodes)), cg)
end

function TheoryInterface.add_term!(cg::ComputeGraph, t::AlgTermId)::Id
  push!(cg.nodes, Node(nothing, t))
  Id(length(cg.nodes))
end

end
