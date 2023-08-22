module TypeLevel

"""
This is used as a supertype for the tag types in a theory that correspond to
type constructors.

Example:

```julia
module Category
struct Ob <: TypTag{1} end
end
```
"""
abstract type TypTag{i} end

getlevel(::TypTag{i}) where {i} = Lvl(i)
getlevel(::Type{<:TypTag{i}}) where {i} = Lvl(i)

"""
This can be used when there isn't a specific struct like `Category.Ob`. Specific
structs are preferred because they make reading backtraces easier.
"""
struct AnonTypTag{i} <: TypTag{i} end

"""
This is used as a supertype for the tag types in a theory that correspond to
the arguments to type constructors

Example:
```julia
module Category
struct dom <: TypArgTag{2,1} end
struct codom <: TypArgTag{2,2} end
```

The first argument is the index of the type constructor, the second is the index
of the argument.
"""
abstract type TypArgTag{i,j} end

"""
This is used as a supertype for the tag types in a theory that correspond to
term constructors.

Example:

```julia
module Category
struct compose <: TrmTag{3} end
end
```
"""
abstract type TrmTag{i} end

getlevel(::TrmTag{i}) where {i} = Lvl(i)
getlevel(::Type{<:TrmTag{i}}) where {i} = Lvl(i)

"""
This can be used when there isn't a specific struct like `Category.compose`. Specific
structs are preferred because they make reading backtraces easier.
"""
struct AnonTrmTag{i} <: TrmTag{i} end

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
gettheory(::T) = ...
```

where `T` is a singleton struct subtyping `AbstractTheory`

Returns the @ref(Theory) associated to `T`.
"""
function gettheory end

"""
A convenience overload of `theory`
"""
gettheory(T::Type{<:AbstractTheory}) = gettheory(T())

end
