module TestTries

using GATlab.Syntax.Tries
import .Tries: node, leaf
using Test

p1 = node(:a => leaf(1), :b => node(:a => leaf(2), :c => leaf(3)))

@test p1.a isa AbstractTrie
@test_throws Tries.TrieDerefError p1[]
@test p1.a[] == 1
@test p1.b.a isa NonEmptyTrie
@test p1.b.a[] == 2

@test sprint(show, p1.a) == "leaf(1)::NonEmptyTrie{Int64}"
@test sprint(show, p1.b) == "NonEmptyTrie{Int64}\n├─ :a ⇒ 2\n└─ :c ⇒ 3\n"

@test ■ == PACKAGE_ROOT
@test ■.a isa TrieVar
@test ■.a.b isa TrieVar
@test_throws Tries.TrieVarNotFound p1[■]

@test p1[■.a] == 1

@test p1[■.b.c] == 3

end
