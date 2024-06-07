# Theories

## What is a GAT?

Generalized Algebraic Theories (GATs) are the backbone of GATlab so let's expand
a bit on GATs and how they fit into the bigger picture of algebra.

An algebraic structure, like a group or category, is a mathematical object
whose axioms all take the form of equations that are universally quantified (the
equations have no exceptions). That’s not a formal definition but it’s a good
heuristic. There are different ways to make this precise. The oldest, going back
to universal algebra in the early 20th centrury, are algebraic theories.

[Universal algebra](https://en.wikipedia.org/wiki/Universal_algebra) (sometimes
called general algebra) is the field of mathematics that studies algebraic
structures themselves, not examples ("models") of algebraic structures.
For instance, rather than take particular groups as the object of study, in
universal algebra one takes the class of groups as an object of study. In an
algebraic theory, you have a collection of (total) operations and they obey a
set of equational axioms. Classically, there is only a single generating type,
but there are also typed or multi-sorted versions of algebraic theories. Most
of the classical structures of abstract algebra, such as groups, rings, and
modules, can be defined as algebraic theories.

Importantly, the theory of categories is [not algebraic](https://
mathoverflow.net/q/354920). In other words, a category cannot be defined as a
(multi-sorted) algebraic theory. The reason is that the operation of composition
is partial, since you can only compose morphisms with compatible (co)domains.
Now, categories sure feel like algebraic structures, so people have come up with
generalizations of algebraic theories that accomodate categories and related
structures.

The first of these was Freyd’s essentially algebraic theories. In an essentially
algebraic theory, you can have partially defined operations; however, to
maintain the equational character of the system, the domains of operations
must themselves be defined equationally. For example, the theory of categories
would be defined as having two types, Ob and Hom, and the composition operation
`compose(f::Hom,g::Hom)::Hom` would have domain given by the equation `codom(f)
== dom(g)`. As your theories get more elaborate, the sets of equations
defining the domains get more complicated and reasoning about the structure
is overwhelming.

Later, Cartmell proposed generalized algebraic theories, which solves the same
problem but in a different way. Rather than having partial operations, you
have total operations but on dependent types (types that are parameterized by
values). So now the composition operation has signature `compose(f::Hom(A,B),
g::Hom(B,C))::Hom(A,C) ⊣ [A::Ob, B::Ob, C::Ob]`  exactly as appears in GATlab.
This is closer to the way that mathematicians actually think and write about
categories. For example, if you look at the definitions of category, functor,
and natural transformation in [Emily Riehl’s textbook](http://www.math.jhu.edu/
~eriehl/context/), you will see that they are already essentially in the form
of a GAT, whereas they require translation into an essentially algebraic theory.
Nevertheless, GATs and essentially algebraic theories have the same expressive
power, at least in their standard set-based semantics. GATs provide a version
of the computer scientist's type theory that plays well with the mathematician's
algebra, thus, providing a perfect opportunity for computer algebra systems.

## The `@theory` macro

GATlab implements a version of the GAT formalism on top of Julia's type system,
taking advantage of Julia macros to provide a pleasant syntax. GATs are defined
using the `@theory` macro.

For example, the theory of categories could be defined by:

```@setup category
using GATlab
```

```@example category
@theory ThCategory begin
  @op begin
    (→) := Hom
    (⋅) := compose
  end
  Ob::TYPE
  Hom(dom::Ob, codom::Ob)::TYPE
  id(A::Ob)::(A → A)
  compose(f::(A → B), g::(B → C))::(A → C) ⊣ [A::Ob, B::Ob, C::Ob]
  (f ⋅ g) ⋅ h == f ⋅ (g ⋅ h) ⊣ [A::Ob, B::Ob, C::Ob, D::Ob,
                                f::(A → B), g::(B → C), h::(C → D)]
  f ⋅ id(B) == f ⊣ [A::Ob, B::Ob, f::(A → B)]
  id(A) ⋅ f == f ⊣ [A::Ob, B::Ob, f::(A → B)]
end
nothing # hide
```

The code is simplified only slightly from the official GATlab definition of
`ThCategory`. The theory has two *type constructors*, `Ob` (object) and `Hom`
(morphism). The type `Hom` is a dependent type, depending on two objects, named
`dom` (domain) and `codom` (codomain). The theory has two *term constructors*,
`id` (identity) and `compose` (composition).

Notice how the return types of the term constructors depend on the argument
values. For example, the term `id(A)` has type `Hom(A,A)`. The term constructor
`compose` also uses *context variables*, listed to the right of the `⊣`
symbol. These context variables can also be defined after a `where` clause,
but the left hand side must be surrounded by parentheses. This allows us to
write `compose(f,g)`, instead of the more verbose `compose(A,B,C,f,g)` (for
discussion, see Cartmell, 1986, Sec 10: Informal syntax).

Notice the `@op` call where we can create method aliases that can then be used
throughout the rest of the theory and outside of definition. We can either use
this block notation, or a single line notation such as `@op (⋅) := compose` to
define a single alias. Here we utilize this functionality by replacing the `Hom`
and `compose` methods with their equivalent Unicode characters, `→` and `⋅`
respectively. These aliases are also automatically available to definitions that
inherit a theory that already has the alias defined.

The result of the `@theory` macro is a module with the following members:

1. For each *declaration* in the theory (which includes term constructors, type constructors, arguments to type constructors (i.e. accessors like `dom` and `codom`), and aliases of the above), a function named with the name of the declaration. These functions are not necessarily original to this module; they may be imported. This allows us to, for instance, use `Base.+` as a method for a theory. For instance, `ThCategory` has functions `Ob, Hom, dom, codom, compose, id, ⋅, →`.

2. A submodule called `Meta` with members:
  - `T`: a zero-field struct that serves as a type-level signifier for the theory.
  - `theory`: a constant of type `GAT` which stores the data of the theory.
  - `@theory`: a macro which expands directly to `theory`, which is used to pass around the data of the theory at macro-expand time.

!!! note

    In general, a GAT consists of a *signature*, defining the types and terms of
    the theory, and a set of *axioms*, the equational laws satisfied by models
    of the theory. The theory of categories, for example, has axioms of
    unitality and associativity. At present, GATlab supports the specification
    of both signatures and the axioms, but only uses the axioms as part of 
    rewriting via e-graphs: it is not automatically checked that models of a GAT
    satisfy the axioms. It is the responsibility of the programmer to ensure this.

#### References

- Cartmell, 1986: Generalized algebraic theories and contextual categories,
  [DOI:10.1016/0168-0072(86)90053-9](https://doi.org/10.1016/0168-0072(86)90053-9)
- Cartmell, 1978, PhD thesis: *Generalized algebraic theories and contextual
  categories*
- Pitts, 1995: Categorical logic, Sec 6: Dependent types
