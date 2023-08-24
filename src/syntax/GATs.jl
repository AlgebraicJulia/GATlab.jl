module GATs
export Constant, AlgTerm, AlgType,
  TypeScope, AlgSort, ArgSorts,
  AlgTermConstructor, AlgTypeConstructor, AlgAxiom,
  JudgmentBinding, GATSegment, GAT

using ..Scopes

using StructEquality


"""
`Constant`

A Julia value in an algebraic context. Checked elsewhere.
"""
@struct_hash_equal struct Constant
  value::Any
end

"""
`AlgTerm`

One syntax tree to rule all the terms.
"""
@struct_hash_equal struct AlgTerm
  head::Union{Reference, Constant}
  args::Vector{AlgTerm}
  function AlgTerm(head::Union{Reference, Constant}, args::Vector{AlgTerm}=EMPTY_ARGS)
    new(head, args)
  end
end

const EMPTY_ARGS = AlgTerm[]

AlgTerm(head::Ident, args::Vector{AlgTerm}=EMPTY_ARGS) = AlgTerm(Reference(head), args)

"""
`AlgType`

One syntax tree to rule all the types.
"""
@struct_hash_equal struct AlgType
  head::Reference
  args::Vector{AlgTerm}
  function AlgType(head::Reference, args::Vector{AlgTerm}=EMPTY_ARGS)
    new(head, args)
  end
end

AlgType(head::Ident, args::Vector{AlgTerm}=EMPTY_ARGS) = AlgTerm(Reference(head), args)

"""
`AlgSort`

A *sort*, which is essentially a type constructor without arguments
"""
@struct_hash_equal struct AlgSort
  ref::Reference
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
`ArgSorts`

A description of the argument sorts for a term constructor, used to disambiguate
multiple term constructors of the same name.
"""
const ArgSorts = Vector{AlgSort}

"""
`JudgmentBinding`

A binding of a judgment to a name and possibly a signature.
"""
const JudgmentBinding = Binding{Judgment, Union{ArgSorts, Nothing}}

"""
`GATSegment`

A piece of a GAT, consisting of a scope that binds judgments to names, possibly
disambiguated by argument sorts.
"""
const GATSegment = Scope{Judgment, Union{ArgSorts, Nothing}}

"""
`GAT`

A generalized algebraic theory. Essentially, just consists of a name and a list
of `GATSegment`s, but there is also some caching to make access faster.
Specifically, there is a dictionary to map ScopeTag to position in the list of
segments, and there are lists of all of the identifiers for term constructors,
type constructors, and axioms so that they can be iterated through faster.
"""
struct GAT <: Context
  name::Symbol
  segments::Vector{GATSegment}
  lookup::Dict{ScopeTag, Int}
  termcons::Vector{Ident}
  typecons::Vector{Ident}
  axioms::Vector{Ident}
end

end
