# Theories

A theory in Gatlab consists of two parts.

1. A Julia value of type `Theory` that describes the theory.
2. A module named by the theory with various Julia types that give us handles
for metaprogramming.

These metaprogramming types include:

- A singleton struct named `Th` and subtyping `AbstractTheory` that has an
   overload of `gettheory` on it returning the Julia value from 1. This is used
   to pass around the entire theory at the type level.
- A singleton struct for each type constructor and term constructor in the
   theory. These are used in place of `Lvl` in types, so that backtraces are
   more readable.

Example:

```julia
module Category
using Gatlab.Theories

struct Th <: AbstractTheory end

Theories.gettheory(::Th) = ...

struct Ob <: TypCon{1} end
struct Hom <: TypCon{2} end

struct compose <: TrmCon{3} end
...
end
```
