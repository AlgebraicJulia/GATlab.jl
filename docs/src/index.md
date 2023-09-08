# GATlab.jl

```@meta
CurrentModule = GATlab
```

`GATlab.jl` is a computer algebra system based on Generalized Algebraic Theories.

Roughly speaking, GATlab consists of two parts. The first part is concerned with *symbolic constructs*. The prototypical symbolic construct is simply a *term*, i.e. a syntax tree. In GATlab, every term is always relative to a *context*, in which the free variables in that term are typed. And the context and term themselves are relative to an underlying theory, which defines the allowable type and term constructors that can be used in contexts and terms, along with laws that allow one to rewrite terms into equivalent other terms.

We think about a term as a symbolic representation of a function from an assignment of values to the free variables to a value for the term. I.e., the term $x^{2} + y^{2}$ represents the function $\mathbb{R}^2 \to \mathbb{R}$ given by $(x,y) \mapsto x^{2} + y^{2}$. However, GATlab also supports higher-level symbolic constructs. For instance, we can consider "substitutions" between contexts, which map free variables in one context to terms in another, as [symbolic functions](https://blog.algebraicjulia.org/post/2023/03/algebraic-geometry-1/), and we can consider a collection of equations between terms in a context as a symbolic relation. We can use these building blocks to build [symbolic dynamical systems](https://blog.algebraicjulia.org/post/2023/05/algebraic-geometry-2/) and other things along these lines. GATlab ensures that all of the manipulation of symbolic constructs is *well-typed*, so that you don't do something like accidently add a vector and a scalar.

The second part of GATlab is concerned with *computational semantics*. The core of computational semantics is *models* of theories. A model tells you:

- When a Julia value is a valid instance of a type in a theory
- How to apply term constructors to Julia values

Given a model for a theory, a term in a context, and values for each of the free variables in that context, one can produce a new value by recursively applying the term constructors; this is known as *interpreting* the term. One can also *compile* the term by producing a Julia function that takes as its arguments values for the free variables in the context and then computes the value of the term. This can be faster than interpreting, because one only has to walk the syntax tree at runtime, not compile time. Analogous operations of interpretation and compilation can also be defined for higher level symbolic constructs. Moreover, GATlab provides facilities for manipulation of *models themselves*. For instance, from a model of a ring, one can construct the model of a module over that ring, where the scalars are ring elements and the vectors are `Vector`s of ring elements.

GATlab is the new backend for [Catlab](https://github.com/AlgebraicJulia/Catlab.jl), and we are currently working to replace the old implementation of GATs with this new one.

There are many programs which have influenced the development of GATlab, here we just list a few

- [MMT](https://uniformal.github.io/doc/)
- [Maude](http://maude.cs.illinois.edu/w/index.php/The_Maude_System:About)
- [Symbolics.jl](https://symbolics.juliasymbolics.org/stable/)
- [Metatheory.jl](https://github.com/JuliaSymbolics/Metatheory.jl)
- [Egg](https://egraphs-good.github.ioj/)
- [Standard ML modules](https://en.wikipedia.org/wiki/Standard_ML)
