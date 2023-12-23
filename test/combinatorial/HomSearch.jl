module TestHomSearch 

using Test
using GATlab
using GATlab.Combinatorial.DataStructs: map_nm, validate, NM, NMI, NMVI, ScopedNMs, Nest
using ..Constructor 

function test_homs(ms, n::Int)
  @test all(is_natural, ms)
  @test length(ms) == n
end 

# Theory Graph (indexed, not fibered)
#####################################
T = ThGraph.Meta.theory
os, hs = sorts(T)

# Discrete hom search
for (a,b) in Iterators.product(1:3,1:3)
  Ga, Gb = create_graph.([a,b])
  test_homs(homomorphisms(Ga,Gb), b ^ a)
end

G_12 = create_graph(2, [(1,2)])
G_12_12 = create_graph(2, [(1,2),(1,2)])

@test isempty(homomorphisms(G_12, G_12_12; epic=[:Hom]))
test_homs(homomorphisms(create_graph(2), create_graph(2); iso=[:Ob]), 2)

G_12_21 = create_graph(2, [(1,2),(2,1)])
G_11 = create_graph(1, [(1,1)])
test_homs(homomorphisms(G_12_21, G_11; monic=[:Hom]), 1)

x = NestedTerm(1, NestedType(hs, [[1,2]]))
y = NestedTerm(1, NestedType(hs, [[2,1]]))
test_homs(homomorphisms(G_12, G_12_12; initial=[x=>y]), 1)
e = NMVI(Int[])
nmi = ScopedNMs(T, Dict(os => NMVI([2,1]), hs=>NMVI(Nest([e NMVI([1]) ;e e ]))))
test_homs(homomorphisms(G_12, G_12_12; initial=nmi), 1)

G_21 = create_graph(2, [(2,1)])
for (a,b) in Iterators.product([G_21,G_12],[G_21,G_12])
  test_homs(homomorphisms(a,b), 1)
  test_homs(homomorphisms(a,b; iso=true), 1)
  test_homs(homomorphisms(a, G_11), 1)
end

test_homs(homomorphisms(G_12_21,G_12_21), 2)

G_cyc3 = create_graph(3, [(1,2),(2,3),(3,1)])
G_cyc6 = create_graph(6, [(1,2),(2,3),(3,4),(4,5),(5,6),(6,1)])
test_homs(homomorphisms(G_cyc6,G_cyc3), 3)
isempty(homomorphisms(G_cyc3, G_cyc6; iso=true))
# ThCategory 
############

walking_arrow = create_category([:a,:b], (f=(:a=>:b),))

test_homs(homomorphisms(walking_arrow, walking_arrow), 3)

# 1->2->3 with an additional generator 1->3
m_123 = create_category([:a,:b,:c], (f=(:a=>:b),g=(:b=>:c), i=(:a=>:c)))
parallel_paths = create_category([:a,:b], (f=(:a=>:b),g=(:a=>:b)))

# Maps out of parallel_paths are pairs of parallel arrows

for x in [m_123, walking_arrow, parallel_paths]
  test_homs(homomorphisms(parallel_paths, x), sum(map_nm(x->x^2, Int, x[hs])))
end

h1 = homomorphism(walking_arrow, parallel_paths)
h2 = homomorphism(parallel_paths, m_123)
h12′ = homomorphism(walking_arrow, m_123)

@test h1[hs] isa ScopedNM{Vector{Int}}

using .ThCategory

C = CombinatorialModelC(ThCategory.Meta.theory)

@withmodel C (id, compose, Ob, Hom) begin
  @test Ob(walking_arrow) isa CombinatorialModel
  @test Hom(h1, walking_arrow, parallel_paths) isa CombinatorialModelMorphism
  @test h12′ == compose(h1,h2)
  @test compose(id(walking_arrow), h1) == h1
end

# Theory Petri 
###############

P11_21 = create_petri([1 0; 0 2], [1 0; 0 1 ])
P11 = create_petri([1 0]', [0 1 ]')
P21 = create_petri([2 0]', [0 1 ]')

test_homs(homomorphisms(P11, P11_21; monic=[:I,:O]), 3)
test_homs(homomorphisms(P21, P11_21; monic=[:I,:O]), 2)

test_homs(homomorphisms(P11, P11_21; iso=[:I,:O]), 1)

# One input species and output species, a 1-1 and a 2-1 transition 
PA = create_petri([1 2; 0 0], [0 0; 1 1])
# Two disjoint 1-in 1-out transitions
PB = create_petri([1 0 ; 0 0;0 1;0 0], [0 0; 1 0; 0 0; 0 1])

test_homs(homomorphisms(PB, PA; iso=[:I,:O]), 1)

end # module
