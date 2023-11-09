using MLStyle
using DataStructures
using StructEquality

using ..Scopes
using ..GATs
using ..ExprInterop

"""
An index into the union-find data structure component of an E-graph. Each
e-class is associated to a set of EIds, including a canonical one. This set is
stored by the union-find.
"""
const EId = Int # TODO make a struct which subtypes integer or roll out our own IntDisjointSets

"""
An EType is in the context of a GAT, which the `head` of the `MethodApp` refers
to. For each parameter there is an e-term.
"""
@struct_hash_equal struct EType
  body::MethodApp{EId}
end

@as_record EType

EType(a::Ident,b::Ident,c::Vector{EId}) = EType(MethodApp(a,b,c))

@struct_hash_equal struct EConstant 
  value::Any
  type::EType
end

@as_record EConstant

"""
ETerms in are interpreted in a GATContext. In the case of a MethodApp, the 
head/method refer to term constructors or accessors of the theory.
"""
@struct_hash_equal struct ETerm
  body::Union{Ident, MethodApp{EId}, EConstant}
end

@as_record ETerm

ETerm(a::Ident,b::Ident,c::Vector{EId}) = ETerm(MethodApp(a,b,c))

const Parents = Dict{ETerm, EId}

"""
`reps` A representation of an equivalence class of e-terms. 
`parents` caches all the e IDs which directly refer to a given term (as opposed 
to some reference in a nested term)
"""
mutable struct EClass
  reps::Set{ETerm}
  type::EType
  parents::Parents
  function EClass(reps::Set{ETerm}, type::EType, parents::Parents=Parents())
    new(reps, type, parents)
  end
end

function add_parent!(ec::EClass, etrm::ETerm, i::EId)
  ec.parents[etrm] = i
end


"""
Stores a congruent partial equivalence relation on terms in the context of
`context`
"""
struct EGraph
  context::GATContext
  eqrel::IntDisjointSets{EId}
  eclasses::Dict{EId, EClass}
  hashcons::Dict{ETerm, EId}
  worklist::Vector{EId}
  isclean::Ref{Bool}
  function EGraph(pres::GATContext)
    new(pres, IntDisjointSets{EId}(0), Dict{EId, EClass}(), Dict{ETerm, EId}(), EId[], Ref(true))
  end
end

EGraph(T::GAT) = EGraph(GATContext(T)) # Theory without any further context

"""
Update e-term to refer to canonical e-ids
"""
function canonicalize!(eg::EGraph, etrm::ETerm)
  (@match etrm.body begin
    x::Union{Constant, Ident} => x
    MethodApp(head, method, args) =>
      MethodApp{EId}(head, method, find_root!.(Ref(eg.eqrel), args))
  end) |> ETerm
end

function etypeof(eg::EGraph, i::EId)
  eg.eclasses[i].type
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

To fix this issue, you should instead declare term constructors like

```
weaken(n, x)::Term(n) ⊣ [n::Nat, x::Term(S(n))]
```
"""
function econtext(eg::EGraph, m::MethodApp{EId})
  termcon = getvalue(eg.context[m.method])
  typeof(termcon) == AlgTermConstructor ||
    error("head of $etrm is not a term constructor")
  length(m.args) == length(termcon.args) ||
    error("wrong number of args for term constructor in $etrm")
  ectx = zeros(EId, length(termcon.localcontext)) 
  # initialize result with top-level arguments
  toexpand = Tuple{AlgType, EType}[]
  for (lid, eid) in zip(termcon.args, m.args)
    ectx[lid.val] = eid
    push!(toexpand, (getvalue(termcon[lid]), etypeof(eg, eid)))
  end
  while !isempty(toexpand)
    (algtype, etype) = pop!(toexpand)
    for (arg, id) in zip(algtype.body.args, etype.body.args)
      id = find_root!(eg.eqrel, id)
      @match arg.body begin
        _::Constant => nothing
        x::Ident => begin
          i = getlid(x).val
          if ectx[i] != 0
            ectx[i] == id ||
              error("contradictory inference of context for $m; could not unify $(ectx[i]) and $id")
          else
            ectx[i] = id
          end
          push!(toexpand, (getvalue(termcon[x]), etypeof(eg, id)))
        end
        _::MethodApp => error("we don't do that kind of thing over here")
      end
    end
  end
  all(!=(0), ectx) || error("could not fully infer context")
  ectx
end

function compute_etype(eg::EGraph, eterm::ETerm)::EType
  @match eterm.body begin
    x::Ident => begin
      algtype = getvalue(eg.context[x]).body
      EType(algtype.head, algtype.method, add!.(Ref(eg), argsof(algtype)))
    end
    c::EConstant => c.type
    m::MethodApp{EId} => begin
      ectx = econtext(eg, m)
      termcon = getvalue(eg.context[m.method])
      type_body = termcon.type.body
      EType(
        type_body.head,
        type_body.method,
        EId[subst!(eg, arg, ectx, gettag(termcon.localcontext)) for arg in type_body.args]
      )
    end
  end
end

"""
Returns the `EId` corresponding to the term resulting from the substitution
in `term` of the idents in the scope refered to by `tag` according to the
values in `ectx`

Note: this is similar logic to `add!`: perhaps combine the two by making `ectx`
and `tag` optional?
"""
function subst!(eg::EGraph, term::AlgTerm, ectx::Vector{EId}, tag::ScopeTag)
  @match term.body begin
    x::Ident && if gettag(x) == tag end => ectx[getlid(x).val]
    c::Union{Constant, Ident} => add!(eg, c)
    m::MethodApp => begin
      args = EId[subst!(eg, arg, ectx, tag) for arg in trm.args]
      add!(eg, ETerm(m.head, m.method, args))
    end
  end
end

"""
Add eterm to an egraph.
"""
function add!(eg::EGraph, eterm::ETerm)
  eterm = canonicalize!(eg, eterm)
  if haskey(eg.hashcons, eterm)
    eg.hashcons[eterm]
  else
    etype = compute_etype(eg, eterm)
    id = push!(eg.eqrel)
    if eterm.body isa MethodApp
      for argid in eterm.body.args
        add_parent!(eg.eclasses[argid], eterm, id)
      end
    end
    eg.hashcons[eterm] = id
    eg.eclasses[id] = EClass(Set([eterm]), etype)
    id
  end
end

function add!(eg::EGraph, term::AlgTerm)
  @match term.body begin
    x::Ident => add!(eg, ETerm(x))
    c::Constant => begin
      tb = c.type.body
      ec = EConstant(c.value, EType(tb.head, tb.method, add!.(Ref(eg), tb.args)))
      add!(eg, ETerm(ec))
    end
    m::MethodApp => add!(eg, ETerm(m.head, m.method, add!.(Ref(eg), m.args)))
  end
end

function add!(eg::EGraph, term::Union{Expr, Symbol})
  add!(eg, fromexpr(eg.context, term, AlgTerm))
end

find!(eg::EGraph, i::EId) = find_root!(eg.eqrel, i)

"""
Merge the eclasses associated with two eIDs. 
"""
function Base.merge!(eg::EGraph, id1::EId, id2::EId)
  eg.isclean[] = false
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

"""
Reinforces the e-graph invariants (i.e., ensures that the equivalence relation
is congruent).
"""
function rebuild!(eg::EGraph)
  while !isempty(eg.worklist)
    todo = [ find!(eg, i) for i in eg.worklist ]
    empty!(eg.worklist)
    for i in todo
      repair!(eg, i)
    end
  end
  eg.isclean[] = true
end

function repair!(eg::EGraph, i::EId)
  for (p_etrm, _) in eg.eclasses[i].parents
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

# Extraction
function extract(eg::EGraph, t::EType; chooser=only)::AlgType
  body = t.body
  AlgType(body.head, body.method, extract.(Ref(eg), body.args; chooser))
end

function extract(eg::EGraph, t::ETerm; chooser=only)::AlgTerm
  @match t.body begin 
    x::Ident => AlgTerm(x)
    c::EConstant => Constant(c.value, extract(eg, c.type; chooser))
    m::MethodApp => AlgTerm(m.head, m.method, extract.(Ref(eg), m.args; chooser))
  end
end

function extract(eg::EGraph, id::EId; chooser=only)::AlgTerm
  extract(eg, chooser(eg.eclasses[id].reps))
end
