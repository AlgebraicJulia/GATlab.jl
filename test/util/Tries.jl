module TestTries

using GATlab.Util.Tries
import .Tries: node, leaf, Node, Leaf, Empty, NonEmpty, zipwith, flatten, fold
using Test
using OrderedCollections

using MLStyle

@test_throws ErrorException Tries.Node_(OrderedDict{Symbol, Int}())

t1 = node(:a => leaf(1), :b => node(:a => leaf(2), :c => leaf(3)))

@test t1.a isa AbstractTrie
@test t1.a == t1[:a]
@test_throws Tries.TrieDerefError t1[]
@test_throws Tries.TrieIndexError t1.z
@test t1.a[] == 1
@test t1.b.a isa NonEmptyTrie
@test t1.b.a[] == 2

@test sprint(show, t1.a) == "leaf(1)::NonEmptyTrie{Int64}"
@test sprint(show, t1.b) == "NonEmptyTrie{Int64}\n├─ :a ⇒ 2\n└─ :c ⇒ 3\n"
@test sprint(show, Trie{Int}()) == "Trie{Int64}()"

@test ■ == PACKAGE_ROOT
@test ■.a isa TrieVar
@test ■.a.b isa TrieVar
@test_throws Tries.TrieVarNotFound t1[■]

@test haskey(t1, ■.a)
@test t1[■.a] == 1

@test t1[■.b.c] == 3

@test sprint(show, ■.a) == "■.a"

@test map(x -> x + 1, leaf(2)) == leaf(3)
@test map(x -> x + 1, Trie{Int}()) == Trie{Int}()

@test filter(x -> x % 2 == 0, t1) == node(:b => node(:a => leaf(2)))
@test filter(_ -> false, Trie{Int}()) == Trie{Int}()

function int_sqrt(x)
  try
    Some(Int(sqrt(x)))
  catch e
    nothing
  end
end

@test filtermap(int_sqrt, Int, t1) == node(:a => leaf(1))
@test filtermap(int_sqrt, Int, Trie{Int}()) == Trie{Int}()

@test t1 == @match t1 begin
  NonEmpty(net1) => net1
end

@test zipwith(+, t1, t1) == node(:a => leaf(2), :b => node(:a => leaf(4), :c => leaf(6)))
# TODO: fix this, zipwith should take an argument for the return type
@test zipwith(+, Trie{Int}(), Trie{Int}()) == Trie{Int}()
@test_throws ErrorException zipwith(+, Trie{Int}(), t1)
@test zip(t1, t1) == node(:a => leaf((1,1)), :b => node(:a => leaf((2,2)), :c => leaf((3,3))))

@test first(t1) == 1
@test_throws ErrorException first(Trie{Int}())

@test hasproperty(t1, :a)
@test !hasproperty(t1, :z)

@test [propertynames(t1)...] == [:a, :b]
@test keys(t1) == propertynames(t1)

@test valtype(t1) == Int
@test valtype(typeof(t1)) == Int
@test eltype(t1) == Int

@test flatten(Trie{Trie{Int}}()) == Trie{Int}()
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
@test mapwithkey((k, _) -> k, TrieVar, Trie{Int}()) == Trie{TrieVar}()

t1_keys = TrieVar[]

traversewithkey((k, _) -> push!(t1_keys, k), t1)

@test t1_keys == [■.a, ■.b.a, ■.b.c]

b = Ref(true)

traversewithkey((_, _) -> b[] = false, Trie{Int}())

@test b[]

@test fold(0, identity, d -> sum(values(d)), t1) == 6
@test fold(0, identity, d -> sum(values(d)), Trie{Int}()) == 0

@test all(iseven, t1) == false
@test all(iseven, filter(iseven, t1))

@test merge(t1, node(:b => node(:z => leaf(4)))) == node(:a => leaf(1), :b => node(:a => leaf(2), :c => leaf(3), :z => leaf(4)))

@test Trie(■.a => 1, ■.b.a => 2, ■.b.c => 3) == t1
@test_throws ErrorException Trie(■.a => 1, ■.a.b => 2)

t2 = node(:a => Trie{Int}())

@test t2 == Trie{Int}()

end
