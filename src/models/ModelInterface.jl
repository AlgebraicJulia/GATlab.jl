module ModelInterface

using ...Syntax

export Model, checkvalidity, typarg, ap

"""
A Julia value with type `Model{T, Tuple{Ts...}}` represents a model of the
theory `T` that has the types `Ts...` assigned to the type constructors in `T`.

Note that we do not expect that structs subtyping `Model` will necessarily be
singletons. In general, they may contain runtime data which is used in the
implementations of the various methods. For instance, this would be the case for
a slice category: the `Model` corresponding to a slice category would have
runtime data of the object that we are slicing over.

An instance of `Model{T, Tuple{Ts...}}` should have overloads for

- `checkvalidity`
- `ap`

as described in the docstrings for each of these methods.
"""
abstract type Model{T <: AbstractTheory, Tup <: Tuple} end

"""
Meant to be overloaded as

```julia
checkvalidity(m::Model{T}, ::TypTag{i}, args..., x) where {T <: AbstractTheory} = ...
```

where:
- `i` is the level of a type constructor in `T`
- `args` are the pre-checked type arguments to the type constructor
- `x` is the value to be checked

Returns a boolean which is true if `x` is a valid element of the type `i` with
type arguments `args...` according to `Model` and false otherwise.

A basic implementation of `checkvalidity` might simply use dispatching on the
type to return true. But in general, it might be necessary to verify runtime
data, for instance checking that something is sorted or something is injective.
"""
function checkvalidity end

"""
If not otherwise specified, we assume that a given value is not valid.
"""
checkvalidity(::Model{<:AbstractTheory}, ::TypTag, args...) = false

"""
Meant to be overloaded as

```julia
ap(m::Model{T}, ::TrmTag{i}, args...; context_args...)
```

where:
- `i` is the level of a term constructor in `T`
- `args` consists of, for each argument to the term constructor `i`, a valid value
of the relevant type
- `context_args` consists of keyword arguments for each of the elements of
the context that are not mentioned in `args`. Sometimes these are needed for
implementation, sometimes they are not, so it is possible to call `ap` without
instantiating all of these and hoping for the best.

Returns the result of applying the term constructor to the arguments, according
to the model `m`. For instance, this is used to compose morphisms, or to get the
identity morphism at an object.

Note that we assume in `ap` that the arguments have already been checked, using
`checkvalidity`.
"""
function ap end

end
