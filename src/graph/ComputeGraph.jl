module ComputeGraphs

struct Id
  index::UInt32
end

struct CGType
  content::Prim.AlgTerm{Id}
end

struct CGTerm
  content::Prim.AlgTerm{Id}
end

struct Node
  name::Union{Symbol, Nothing} # only for debugging purposes
  term::Union{CGTerm, Nothing} # some nodes aren't defined in terms of other nodes
  type::CGType
end

struct ComputeGraph{Ts} <: Model{Ts}
  theory::GAT
  nodes::Vector{Node}
end

function getindex(cg::ComputeGraph, i::Id)
  cg.nodes[i.index]
end

function add_node!(cg::ComputeGraph, n::Node)::Id
  push!(cg.nodes, n)
  Id(length(cg.nodes))
end

struct CGVar{T}
  id::Id
  cg::ComputeGraph
end

function getindex(v::CGVar)
  v.cg[v.id]
end

macro cg_model(theory_module)
  # derive a model instance for ComputeGraph{Tuple{CGVar{T1}, ..., CGVar{TN}}}
  # where T1,...,TN are the type functions found in the module.
end

end
