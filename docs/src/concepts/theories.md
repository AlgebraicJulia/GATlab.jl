# Theories

The result of the `@theory` macro is a module with the following members:

1. For each *declaration* in the theory (which includes term constructors, type constructors, arguments to type constructors (i.e. accessors like `dom` and `codom`), and aliases of the above), a function named with the name of the declaration. These functions are not necessarily original to this module; they may be imported. This allows us to, for instance, use `Base.+` as a method for a theory. For instance, `ThCategory` has functions `Ob, Hom, dom, codom, compose, id, ⋅`.
2. A submodule called `Meta` with members:
  - `T`: a zero-field struct that serves as a type-level signifier for the theory
  - `theory`: a constant of type `GAT` which stores the data of the theory.
  - `@theory`: a macro which expands directly to `theory`, which is used to pass around the data of the theory at macro-expand time.
