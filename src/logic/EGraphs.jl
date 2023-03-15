module EGraphs
export EGraph, add!, rebuild!

using DataStructures
using StructEquality

using ...Syntax

const Id = Int

@struct_hash_equal struct ETrm
  head::Lvl
  args::Vector{Id}
end

const Parents = Dict{ETrm, Id}

mutable struct EClass
  reps::Set{ETrm}
  parents::Parents
end

function add_parent!(ec::EClass, etrm::ETrm, i::Id)
  ec.parents[etrm] = i
end

struct EGraph
  eqrel::IntDisjointSets{Id}
  eclasses::Dict{Id, EClass}
  hashcons::Dict{ETrm, Id}
  worklist::Vector{Id}
  function EGraph()
    new(IntDisjointSets(0), Dict{Id, EClass}(), Dict{ETrm, Id}(), Id[])
  end
end

function canonicalize!(eg::EGraph, etrm::ETrm)
  ETrm(etrm.head, find_root!.(Ref(eg.eqrel), etrm.args))
end

function add!(eg::EGraph, etrm::ETrm)
  etrm = canonicalize!(eg, etrm)
  if etrm ∈ keys(eg.hashcons)
    eg.hashcons[etrm]
  else
    id = push!(eg.eqrel)
    for i in etrm.args
      add_parent!(eg.eclasses[i], etrm, id)
    end
    eg.hashcons[etrm] = id
    eg.eclasses[id] = EClass(Set([etrm]), Parents())
    id
  end
end

function add!(eg::EGraph, trm::Trm)
  add!(eg, ETrm(trm.head, add!.(Ref(eg), trm.args)))
end

find!(eg::EGraph, i::Id) = find_root!(eg.eqrel, i)

function Base.merge!(eg::EGraph, id1::Id, id2::Id)
  if (i = find!(eg, id1)) == find!(eg, id2)
    return i
  end

  id = union!(eg.eqrel, id1, id2)
  id1, id2 = (id == id1) ? (id2, id1) : (id1, id2)
  push!(eg.worklist, id)
  ec1 = eg.eclasses[id1]
  ec2 = eg.eclasses[id2]
  union!(ec2.reps, ec1.reps)
  merge!(ec2.parents, ec1.parents)
  delete!(eg.eclasses, id1)
  id
end

function rebuild!(eg::EGraph)
  while !isempty(eg.worklist)
    todo = [ find!(eg, i) for i in eg.worklist ]
    empty!(eg.worklist)
    for i in todo
      repair!(eg, i)
    end
  end
end

function repair!(eg::EGraph, i::Id)
  for (p_etrm, p_eclass) in eg.eclasses[i].parents
    delete!(eg.hashcons, p_etrm)
    p_etrm = canonicalize!(eg, p_etrm)
    eg.hashcons[p_etrm] = find!(eg, i)
  end

  new_parents = Parents()

  for (p_etrm, p_eclass) in eg.eclasses[i].parents
    p_etrm = canonicalize(eg, p_etrm)
    if p_etrm ∈ keys(new_parents)
      merge!(eg, p_eclass, new_parents[p_etrm])
    end
    new_parents[p_etrm] = find!(eg, p_eclass)
  end

  eg.eclasses[i].parents = new_parents
end

end
