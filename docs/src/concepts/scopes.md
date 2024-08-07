# Scopes

Design rationale:

Namespacing, i.e. references which look like `britain.economy.GDP`, should be
first class. This doesn't play nicely with the internal representation of names
via [deBruijn levels](https://en.wikipedia.org/wiki/De_Bruijn_index); we don't
want to do a bunch of math to convert between flattened and nested versions
of contexts. Conceptually, we should then switch our identifiers to be *lists*
of deBruijn levels.

But there are also significant subtleties in the translation between named and
nameless representations of identifiers. Also in practice if we are referencing
something that might change over time, like a C-set, we don't want to use
deBruijn levels, because we don't want have to change all of our identifiers
when we delete something, so in the rest of this I will instead say "local
identifier" instead of deBruijn level to refer to a nameless representation of
an identifier.

(the name "local identifier" and also some of this philosophy is taken from
[chit](https://github.com/davidad/chit))

In general, naming is given by a *relation* between symbols and *bindings* (as
referred to by local identifiers).  Each binding may be associated with zero or
more symbols, and each symbol might be associated with zero or more bindings.

We name the failure of this relation to be a bijection in several ways.

- If more than one symbol is related to a single binding, we say that this
binding has *aliases*. In this case, we should also have a *primary alias*
used as a default.
- If more than one binding is related to a single symbol, we have *name overlap*.
Name overlap can be resolved by *overloading* and *shadowing*, we will talk
about this later on.
- If no symbol is related to a binding, such as when the binding is created
programmatically, we need *nameless references* to be able to refer to the
binding, which are also created programmatically.
- If no binding is related to a symbol, then we have a *name error*; this name
is not valid in the current context and we must throw an error.

The most important thing to get right is *name overlap*; we discuss this first.

There are two ways in which to resolve name overlap.  The first way is via
*overloading*. In overloading, we disambiguate an ambiguous name via its
context, for instance what type it is expected to be, or what arguments is it
receiving. The second way is via *shadowing*. In shadowing, a name is resolved
by making it point to the "most recently defined" thing with that name.

In GATlab, we handle overloading and shadowing with a notion of *scope*.
Anything which binds variables introduces a scope, for instance a `@theory`
declaration or a context. Each scope is identified with a ScopeTag, which is an
opaque identifier (i.e. a UUID). We take this idea from Racket, but we don't
need the more complex "scope sets" from Racket because GATs don't need to
process the syntax of other GATs; if we start doing this we'll have to rethink
the design, but we'll probably have bigger problems too.

Two variables with the same name within a single scope are meant to overload one
another. For instance, this is what happens with `mcompose` in the theory of
monoidal categories; it is overloaded for `Hom` and `Ob`, and this is what
happens with `d` in the discrete exterior calculus; it is overloaded for all of
the (k+1)-forms. Variables in different scopes with the same name *shadow* one
another. When we parse an expression `a + b`, we do so in an ordered list of
scopes, and the most recent scope "wins".

Parsing turns a `Symbol` into an `Ident`. The `Ident` contains the original
`Symbol` for printing, but it also contains a reference to a scope via ScopeTag,
and an local identifier ("lid") within that scope. Thus, the name in the `Ident`
is never needed for later stages of programmatic manipulation.

Scopes cache the relation between names and bindings, by providing a way to go
from binding (as reified by local identifier) to a set of aliases with
distinguished primary alias, and to go from name to the set of bindings that
have that name that we need to disambiguate between in the case of an overload.

Because `Ident`s are fully unambiguous even without their name, it is also possible
to create an `Ident` with no name, which solves the problem of *nameless references*.
