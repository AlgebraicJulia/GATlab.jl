module EGraphs
export EGraph, ETrm, ETyp, EClass, Id, add!, rebuild!, find!

using MLStyle
using DataStructures
using StructEquality

using ...Syntax

const Id = Int

@struct_hash_equal struct ETrm
  head::Lvl
  args::Vector{Id}
end

@as_record ETrm

@struct_hash_equal struct ETyp
  head::Lvl
  args::Vector{Id}
end

@as_record ETyp

const Parents = Dict{ETrm, Id}

mutable struct EClass
  reps::Set{ETrm}
  parents::Parents
  typ::ETyp
end

function add_parent!(ec::EClass, etrm::ETrm, i::Id)
  ec.parents[etrm] = i
end

# TODO: also add a "context" field to this, so that we don't have to extend the
# Theory

struct EGraph
  theory::Theory
  eqrel::IntDisjointSets{Id}
  eclasses::Dict{Id, EClass}
  hashcons::Dict{ETrm, Id}
  worklist::Vector{Id}
  function EGraph(theory::Theory)
    new(theory, IntDisjointSets(0), Dict{Id, EClass}(), Dict{ETrm, Id}(), Id[])
  end
end

function EGraph(T::Type{<:AbstractTheory})
  EGraph(gettheory(T))
end

function canonicalize!(eg::EGraph, etrm::ETrm)
  ETrm(etrm.head, find_root!.(Ref(eg.eqrel), etrm.args))
end

function typof(eg::EGraph, i::Id)
  eg.eclasses[i].typ
end

"""
This computes the inferred context for an etrm.

For example, if `f` is an id with etyp `Hom(x,y)` and `g` is an id with etyp
`Hom(y,z)`, then context(eg, :(g ∘ f)) computes the context `[x,y,z,f,g]`.

The tricky thing comes from term formers like

weaken(x)::Term(n) ⊣ [n::Nat, x::Term(S(n))]

We get the ETyp for x from the e-graph, and then we have to ematch its argument
with `S(n)` to figure out what `n` is... The problem is that in general `S` will
not be injective, so this is ambiguous!

What we are going to do for now is say that types in the context of a term former
can't be nested. I.e., we only allow types of the form `Term(n)`, not `Term(S(n))`.

Fortunately, I don't think we care about any theories with this kind of context
former.
"""
function context(eg::EGraph, etrm::ETrm)
  j = eg.theory[etrm.head]
  trmcon = j.head
  typeof(trmcon) == TrmCon ||
    error("head of $etrm is not a term constructor")
  length(etrm.args) == length(trmcon.args) ||
    error("wrong number of args for term constructor in $etrm")
  ctx = zeros(Id, length(j.ctx))
  toexpand = Tuple{Typ, ETyp}[]
  for (argidx, id) in zip(trmcon.args, etrm.args)
    ctx[index(argidx)] = id
    push!(toexpand, (j.ctx[argidx][2], typof(eg, id)))
  end
  while !isempty(toexpand)
    (typ, etyp) = pop!(toexpand)
    for (argtrm, id) in zip(typ.args, etyp.args)
      id = find_root!(eg.eqrel, id)
      hd = argtrm.head
      # if this is a variable in the context
      if is_context(hd)
        if ctx[index(hd)] != 0
          ctx[index(hd)] == id ||
            error("contradictory inference of context for $etrm; could not unify $(ctx[hd - n]) and $id")
        else
          ctx[index(hd)] = id
        end
        push!(toexpand, (j.ctx[hd][2], typof(eg, id)))
      # if this is a general term
      else
        # TODO: implement maxref
        # maxref(trm) < n ||
        #   error("we do not yet support nested reference to context terms in term formers")
      end
    end
  end
  all(ctx .!= 0) || error("could not fully infer context")
  ctx
end

function compute_etyp(eg::EGraph, etrm::ETrm)
  ctx = context(eg, etrm)
  j = eg.theory[etrm.head]
  ETyp(j.head.typ.head, Id[subst(eg, arg, ctx) for arg in j.head.typ.args])
end

function subst(eg::EGraph, trm::Trm, ctx::Vector{Id})
  if is_context(trm.head)
    ctx[index(trm.head)]
  else
    args = Id[subst(eg::EGraph, arg, ctx) for arg in trm.args]
    add!(eg, ETrm(trm.head, args))
  end
end

function add!(eg::EGraph, etrm::ETrm)
  etrm = canonicalize!(eg, etrm)
  if etrm ∈ keys(eg.hashcons)
    eg.hashcons[etrm]
  else
    etyp = compute_etyp(eg, etrm)
    id = push!(eg.eqrel)
    for i in etrm.args
      add_parent!(eg.eclasses[i], etrm, id)
    end
    eg.hashcons[etrm] = id
    eg.eclasses[id] = EClass(Set([etrm]), Parents(), etyp)
    id
  end
end

function add!(eg::EGraph, trm::Trm)
  add!(eg, ETrm(trm.head, add!.(Ref(eg), trm.args)))
end

find!(eg::EGraph, i::Id) = find_root!(eg.eqrel, i)

function Base.merge!(eg::EGraph, id1::Id, id2::Id)
  id1, id2 = find!.(Ref(eg), (id1, id2))
  if id1 == id2
    return id1
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
