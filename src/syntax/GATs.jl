module GATs
export Constant, AlgTerm, AlgType,
  TypeScope, AlgSort, AlgSorts,
  AlgTermConstructor, AlgTypeConstructor, AlgAxiom,
  JudgmentBinding, GATSegment, GAT, sortcheck, allnames

using ..Scopes

using StructEquality

"""
We need this to resolve a mutual reference loop; the only subtype is Constant
"""
abstract type AbstractConstant end

"""
`AlgTerm`

One syntax tree to rule all the terms.
Head reference can be a AlgTermConstructor, Binding{AlgType, Nothing}, AbstractConstant
"""
@struct_hash_equal struct AlgTerm
  head::Union{Reference, AbstractConstant}
  args::Vector{AlgTerm}
  function AlgTerm(head::Union{Reference, AbstractConstant}, args::Vector{AlgTerm}=EMPTY_ARGS)
    new(head, args)
  end
end

const EMPTY_ARGS = AlgTerm[]

AlgTerm(head::Ident, args::Vector{AlgTerm}=EMPTY_ARGS) = AlgTerm(Reference(head), args)

"""
`AlgType`

One syntax tree to rule all the types.
`head` must be reference to a `AlgTypeConstructor`
"""
@struct_hash_equal struct AlgType
  head::Reference
  args::Vector{AlgTerm}
  function AlgType(head::Reference, args::Vector{AlgTerm}=EMPTY_ARGS)
    new(head, args)
  end
end

AlgType(head::Ident, args::Vector{AlgTerm}=EMPTY_ARGS) = AlgType(Reference(head), args)

"""
`Constant`

A Julia value in an algebraic context. Checked elsewhere.
"""
@struct_hash_equal struct Constant
  value::Any
  type::AlgType
end

"""
`AlgSort`

A *sort*, which is essentially a type constructor without arguments
`ref` must be reference to a `AlgTypeConstructor`
"""
@struct_hash_equal struct AlgSort
  ref::Reference
end

AlgSort(i::Ident) = AlgSort(Reference(i))

function AlgSort(c::Context, t::AlgTerm)
  if t.head isa AbstractConstant
    AlgSort(t.head.type.head)
  else
    binding = c[only(t.head)]
    value = getvalue(binding)
    if value isa AlgType
      AlgSort(value.head)
    elseif value isa AlgTermConstructor
      AlgSort(value.type.head)
    else
      error("head of AlgTerm $value is not a term constructor or variable")
    end
  end
end

"""
`Context`

A scope where variables are assigned to `AlgType`s, and no overloading is
permitted.
"""
const TypeScope = Scope{AlgType, Nothing}

"""
`SortContext`

A scope where variables are assigned to `AlgSorts`s, and no overloading is
permitted.
"""
const SortScope = Scope{AlgSort, Nothing}

"""`sortcheck(ctx::Context, t::AlgTerm)`

Throw an error if a the head of an AlgTerm (which refers to a term constructor)
has arguments of the wrong sort. Returns the sort of the term.
"""
function sortcheck(ctx::Context, t::AlgTerm)::AlgSort
  if t.head isa Reference
    ref = ctx[t.head] |> getvalue
    if ref isa AlgType
      isempty(t.args) || error("Cannot apply a variable to arguments: $t")
    elseif ref isa AlgTermConstructor
      argsorts = sortcheck.(Ref(ctx), t.args)
      argsorts == AlgSort.([a.head for a in getvalue.(ref.args)]) || error("Sorts don't match")
    else 
      error("Unexpected reference type $ref for AlgTerm $t")
    end
  elseif t.head isa Constant
  else 
    error("Unexpected head for AlgTerm")
  end
  return AlgSort(ctx, t)
end

"""`sortcheck(ctx::Context, t::AlgType)`

Throw an error if a the head of an AlgType (which refers to a type constructor)
has arguments of the wrong sort.
"""
function sortcheck(ctx::Context, t::AlgType)
  ref = ctx[t.head] |> getvalue
  ref isa AlgTypeConstructor || error("AlgType head must refer to AlgTypeConstructor: $ref")
  argsorts = sortcheck.(Ref(ctx), t.args)
  expected = AlgSort.([a.head for a in getvalue.(ref.args)])
  argsorts == expected || error("Sorts don't match: $argsorts != $expected")
end

"""
`AlgTypeConstructor`

A declaration of a type constructor
"""
@struct_hash_equal struct AlgTypeConstructor
  localcontext::TypeScope
  args::TypeScope
end

"""
`AlgTermConstructor`

A declaration of a term constructor
"""
@struct_hash_equal struct AlgTermConstructor
  localcontext::TypeScope
  args::TypeScope
  type::AlgType
end

"""
`AlgAxiom`

A declaration of an axiom
"""
@struct_hash_equal struct AlgAxiom
  localcontext::TypeScope
  type::AlgType
  equands::Vector{AlgTerm}
end

"""
`Judgment`

A judgment is either a type constructor, term constructor, or axiom; a GAT
is composed of a list of judgments.
"""
const Judgment = Union{AlgTypeConstructor, AlgTermConstructor, AlgAxiom}

"""
`AlgSorts`

A description of the argument sorts for a term constructor, used to disambiguate
multiple term constructors of the same name.
"""
const AlgSorts = Vector{AlgSort}

"""
`JudgmentBinding`

A binding of a judgment to a name and possibly a signature.
"""
const JudgmentBinding = Binding{Judgment, Union{AlgSorts, Nothing}}

"""
`GATSegment`

A piece of a GAT, consisting of a scope that binds judgments to names, possibly
disambiguated by argument sorts.
"""
const GATSegment = Scope{Judgment, Union{AlgSorts, Nothing}}

function allnames(seg::GATSegment)
  names = Symbol[]
  for binding in seg
    judgment = getvalue(binding)
    if judgment isa AlgTermConstructor
      push!(names, nameof(binding))
    elseif judgment isa AlgTypeConstructor
      push!(names, nameof(binding))
      for argbinding in judgment.args
        push!(names, nameof(argbinding))
      end
    end
  end
  names
end

"""
`GAT`

A generalized algebraic theory. Essentially, just consists of a name and a list
of `GATSegment`s, but there is also some caching to make access faster.
Specifically, there is a dictionary to map ScopeTag to position in the list of
segments, and there are lists of all of the identifiers for term constructors,
type constructors, and axioms so that they can be iterated through faster.

GATs allow overloading but not shadowing.
"""
struct GAT <: Context
  name::Symbol
  segments::ScopeList{Judgment, Union{AlgSorts, Nothing}}
  termcons::Vector{Ident}
  typecons::Vector{Ident}
  axioms::Vector{Ident}
  function GAT(name::Symbol, segments::Vector{GATSegment})
    termcons = Ident[]
    typecons = Ident[]
    axioms = Ident[]
    names = Set{Symbol}()
    for segment in segments
      if !isempty(intersect(keys(segment.names), names))
        error("We do not permit shadowing of names between segments of a GAT")
      end
      union!(names, keys(segment.names))
      for (i, binding) in enumerate(segment)
        x = ident(segment, i)
        judgment = getvalue(binding)
        if judgment isa AlgTermConstructor
          push!(termcons, x)
        elseif judgment isa AlgTypeConstructor
          push!(typecons, x)
        else
          push!(axioms, x)
        end
      end
    end
    new(name, ScopeList(segments), termcons, typecons, axioms)
  end

  # This could be faster, but it's not really worth worrying about
  function GAT(name::Symbol, parent::GAT, newsegment::GATSegment)
    GAT(name, [parent.segments.scopes..., newsegment])
  end
end

Scopes.getscopes(c::GAT) = getscopes(c.segments)

Scopes.scopelevel(c::GAT, t::ScopeTag) = scopelevel(c.segments, t)
Scopes.scopelevel(c::GAT, s::Symbol) = scopelevel(c.segments, s)

Base.length(c::GAT) = length(c.segments)
Base.getindex(c::GAT, x::Ident) = getindex(c.segments, x)
Base.getindex(c::GAT, i::Int) = getindex(c.segments, i)

Scopes.ident(c::GAT, level::Int; name=nothing, scopelevel::Union{Int, Nothing}=nothing) =
  ident(c.segments, level; name, scopelevel)

Scopes.ident(c::GAT, name::Symbol; sig=nothing, scopelevel::Union{Int, Nothing}=nothing) =
  ident(c.segments, name; sig, scopelevel)

function allnames(theory::GAT)
  vcat(allnames.(theory.segments)...)
end


end
