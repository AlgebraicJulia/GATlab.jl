# Model families

The semantics part of GATlab is the *model family* infrastructure.

Given a theory, one can declare a model family for that theory. This consists of the following.

1. A struct `T`. Each value of the struct is a *model* of the theory. The struct subtypes `Model{Th, Tuple{Ts...}}`. `Th` is the theory that the struct is a model family for, and `Ts` specifies types for each of the type constructors in `Theory`.
2. For each type constructor `i` in `Theory`, an overload of `checkvalidity` of the form
   
   ```julia
   checkvalidity(m::T, ::TypCon{i}, args..., val) = ...
   ```
   
   This checks that `val` is a valid instance of `i` applied to `args...`, assuming that `args...` have been previously checked to be valid.

   This can then be applied using, for instance

   ```julia
   checkvalidity(m, Category.Hom, x, y, f)
   ```

   using the singleton structs defined in [Theories](@ref)
3. For each term constructor `i` in `Theory`, an overload of `ap` of the form

   ```julia
   ap(m::T, ::TrmCon{i}, args...) = ...
   ```
    
   Here `args...` is to be interpreted as elements of the full context of the term constructor, not just the direct arguments of the term constructor itself. The reason for this is that the implementation of `ap` might need the data of, say, the domain and codomain of morphisms in order to compose them, and because we have an indexed form of dependent types, this information is not available from the morphism data itself.
