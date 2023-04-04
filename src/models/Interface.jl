module Interface
export AbstractTheory, theory, Model, checkvalidity, typarg, ap

"""
A type-level signifier for a particular theory, used to control dispatch
and to pass around theory objects (which can't be type parameters) at
the type level.

Structs which subtype `AbstractTheory` should always be singletons, and
have `theory` defined on them.
"""
abstract type AbstractTheory end

"""
Meant to be overloaded as

```julia
theory(::T) = ...
```

where `T` is a singleton struct subtyping `AbstractTheory`

Returns the @ref(Theory) associated to `T`.
"""
function theory end

"""
A convenience overload of `theory`
"""
theory(T::Type{<:AbstractTheory}) = theory(T())

"""
An element of `Model{T}` represents a model of the theory `T`.

Note that unlike with `AbstractModel`, we do not expect that structs subtyping
`Model` will necessarily be singletons. In general, they may contain runtime
data which is used in the implementations of the various methods. For instance,
this would be the case for a slice category: the `Model` corresponding to a
slice category would have runtime data of the object that we are slicing over.

An instance of `Model{T}` should have overloads for

- `checkvalidity`
- `typarg`
- `ap`

as described in the docstrings for each of these methods.
"""
abstract type Model{T <: AbstractTheory} end

"""
Meant to be overloaded as

```julia
checkvalidity(m::Model{T}, ::Var{i}, x) where {T <: AbstractTheory} = ...
```

where:
- `i` is the level of a type constructor in `T`
- `x` is an arbitrary Julia value

Returns a boolean which is true if `x` is a valid element of the type `i`
according to `Model` and false otherwise.

If the type `i` has arguments, an implementation of `checkvalidity` can
assume that they have already been checked.

A basic implementation of `checkvalidity` might simply use dispatching on the
type to return true. But in general, it might be necessary to verify runtime
data, for instance checking that something is sorted or something is injective.
"""
function checkvalidity end

"""
If not otherwise specified, we assume that a given value is not valid.
"""
checkvalidity(::Model{<:AbstractTheory}, ::Var, _) = false

"""
Meant to be overloaded as

```julia
typarg(m::Model{T}, ::Var{i}, ::Var{j}, x) where {T <: AbstractTheory} = ...
```

where:
- `i` is the level of a type constructor in `T`
- `j` is an integer representing the index of the argument
- `x` is a possibly invalid of the type `i`

Returns the value of the type argument `j` for the type constructor `i`. For
instance, this might return the domain/codomain of a morphism. Returns `nothing`
if `typarg` can't figure out this value.

Checking of a term `t` procedes as follows:

- get type arguments
- check validity of type arguments
- check validity of `t`

So we can't assume that `typarg` will be passed valid data. The only guarantee
that `typarg` should make is that it returns the correct arguments given valid
data. If given invalid data, `typarg` can output invalid data, or `nothing`.

`checkvalidity` on the other hand, must reject invalid data.
"""
function typarg end

"""
Meant to be overloaded as

```julia
ap(m::Model{T}, ::Var{i}, xs...)
```

where:
- `i` is the level of a term constructor in `T`
- `xs` consists of, for each argument to the term constructor `i`, a valid value
of the relevant type

Returns the result of applying the term constructor to the arguments, according
to the model `m`. For instance, this is used to compose morphisms, or to get the
identity morphism at an object.

Note that we assume in `ap` that the arguments have already been checked, using
`checkvalidity` and `typarg`.
"""
function ap end

end
