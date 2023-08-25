module ModelInterface

using ...Syntax

export Model, checkvalidity, typarg, ap

"""
`Model{Tup <: Tuple}`

A Julia value with type `Model{Tuple{Ts...}}` represents a model of some
part of the theory hierarchy, which uses the types in `Ts...` to implement
the sorts.

A model `m::Model{Tup}` implements a `seg::GATSegmant` iff `implements(m,
Val(gettag(seg))) == true`, and then we expect that all of the functions in the
module corresponding to `seg` are overloaded for the keyword argument
`;model::typeof(m)`.

A model `m::Model{Tup}` implements a theory iff it implements all of the GATSegments
in the theory.
"""
abstract type Model{Tup <: Tuple} end

"""
`implements(m::Model, tag::ScopeTag) -> Boolean`

Hooks into
"""
implements(m::Model, tag::ScopeTag) = implements(m, ::Type{Val{tag}})

end
