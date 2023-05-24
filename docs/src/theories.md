# Theories

A theory in Gatlab consists of two parts.

1. A Julia value of type `Theory` that describes the theory.
2. Various Julia types to aid in metaprogramming with the theory, such as:
   - A singleton struct named after the theory that has an overload of
   `gettheory` on it returning the Julia value from 1. This is used to pass
   around the entire theory at the type level.
   - A module with a singleton struct for each type constructor and term
   constructor in the theory. These are used in place of `Lvl` in types, so
   that backtraces are more readable.
   
   Example
   ```julia
   module Category
   struct Ob <: TypCon{1} end
   struct Hom <: TypCon{2} end
   ...
   end
   ```
