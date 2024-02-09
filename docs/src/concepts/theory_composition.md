# Theory Composition

As theories get larger, it becomes more and more important to not build the
entire theory from scratch. Not only is this tedious, it is also error-prone.
From the beginning, Catlab and GATlab have supported single inheritance, which
helps to some extent. In this document, we lay out other approaches to composing
theories.

## Multiple Inheritance

In a GATlab `@theory`, one can use `using` to take the *union* of one theory
with another theory.

The way this works is the following. Every time a new theory is created, the new
definitions for that theory form a new scope, with a unique UUID. Union of
theories operates on a scope tag level, taking the union of the sets of UUIDs
and then producing a theory with all the bindings from the scopes tagged by
those UUIDs.

If we never had to parse user-supplied expressions, then the names of the
operations in the theories wouldn't matter, because identifiers come with scope
tags. However, as a practical matter, we disallow unioning two theories with the
same name declaration.

That being said, it is fine to union two theories which *overload* the same
declaration. That is, if two theories have the declaration of a name in common,
then they can overload that name as long as they don't give conflicting
overloads, in the same way that overloading methods in Julia works.

This is akin to the way multiple inheritance works in frameworks such as

- Haskell typeclasses
- [Object-oriented systems with multiple inheritance, like Scala](https://docs.scala-lang.org/scala3/book/domain-modeling-tools.html#traits)
- [Module inclusion in OCaml](https://cs3110.github.io/textbook/chapters/modules/includes.html)

## Nesting

However, there are other ways of composing things like GATlab theories. In
dependently typed languages used for theorem proving, algebraic structures are
often represented by dependent records. For instance, in the agda unimath
library, the [definition of a group](https://github.com/UniMath/agda-unimath/blob/master/src/group-theory/groups.lagda.md) is

```agda
Semigroup :
  (l : Level) → UU (lsuc l)
Semigroup l = Σ (Set l) has-associative-mul-Set

Group :
  (l : Level) → UU (lsuc l)
Group l = Σ (Semigroup l) is-group
```
