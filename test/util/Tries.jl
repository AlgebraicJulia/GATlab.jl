module TestTries

using GATlab.Util.Tries
import .Tries: node, leaf, Node, Leaf, Empty, NonEmpty, zipwith, flatten, fold
using Test

using MLStyle

t1 = node(:a => leaf(1), :b => node(:a => leaf(2), :c => leaf(3)))

@test t1.a isa AbstractTrie
@test_throws Tries.TrieDerefError t1[]
@test t1.a[] == 1
@test t1.b.a isa NonEmptyTrie
@test t1.b.a[] == 2

@test sprint(show, t1.a) == "leaf(1)::NonEmptyTrie{Int64}"
@test sprint(show, t1.b) == "NonEmptyTrie{Int64}\n├─ :a ⇒ 2\n└─ :c ⇒ 3\n"

@test ■ == PACKAGE_ROOT
@test ■.a isa TrieVar
@test ■.a.b isa TrieVar
@test_throws Tries.TrieVarNotFound t1[■]

@test t1[■.a] == 1

@test t1[■.b.c] == 3

@test filter(x -> x % 2 == 0, t1) == node(:b => node(:a => leaf(2)))

function int_sqrt(x)
  try
    Some(Int(sqrt(x)))
  catch e
    nothing
  end
end

@test filtermap(int_sqrt, Int, t1) == node(:a => leaf(1))

@test t1 == @match t1 begin
  NonEmpty(net1) => net1
end

@test zipwith(+, t1, t1) == node(:a => leaf(2), :b => node(:a => leaf(4), :c => leaf(6)))
@test zip(t1, t1) == node(:a => leaf((1,1)), :b => node(:a => leaf((2,2)), :c => leaf((3,3))))


@test flatten(leaf(t1)) == t1
@test flatten(leaf(leaf(1))) == leaf(1)
@test flatten(node(:f => leaf(leaf(1)), :g => leaf(t1))) ==
  node(
    :f => leaf(1)
  , :g => node(
            :a => leaf(1)
          , :b => node(
                    :a => leaf(2)
                  , :c => leaf(3)
                  )
          )
  )

@test mapwithkey((k, _) -> k, TrieVar, t1) == node(:a => leaf(■.a), :b => node(:a => leaf(■.b.a), :c => leaf(■.b.c)))

keys = TrieVar[]

traversewithkey((k, _) -> push!(keys, k), t1)

@test keys == [■.a, ■.b.a, ■.b.c]

@test fold(0, identity, d -> sum(values(d)), t1) == 6
@test fold(0, identity, d -> sum(values(d)), Trie{Int}()) == 0

@test all(iseven, t1) == false
@test all(iseven, filter(iseven, t1))

@test merge(t1, node(:z => leaf(4))) == node(:a => leaf(1), :b => node(:a => leaf(2), :c => leaf(3)), :z => leaf(4))

@test Trie(■.a => 1, ■.b.a => 2, ■.b.c => 3) == t1

t2 = node(:a => Trie{Int}())

@test t2 == Trie{Int}()

end
