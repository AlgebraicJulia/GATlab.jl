module TestLimits 

using Test
using GATlab
using GATlab.Combinatorial.DataStructs: TermIterator, TypeIterator
using ..Constructor 

# ThGraph
#########

G_1212 = create_graph(2, [(1,2),(1,2)])
G_12_2323 = create_graph(3, [(1,2),(2,3),(2,3)])
G_1212_2323 = create_graph(3, [(1,2),(1,2),(2,3),(2,3)])

T = ThGraph.Meta.theory
os, hs = sorts(T)
e1, e2 = NestedTerm.(1:2, Ref(NestedType(hs, [[1,2]])))
e3, e4 = NestedTerm.(1:2, Ref(NestedType(hs, [[2,3]])))

f = homomorphism(G_1212, G_12_2323; initial=[e1=>e3,e2=>e4])
g = homomorphism(G_1212, G_1212_2323; initial=[e1=>e2,e2=>e2])

@test getvalue(getvalue(f[:Ob])) == [2,3]
@test getvalue(getvalue(g[:Ob])) == [1,2]
@test getindex.(Ref(f[:Hom]),[e1,e2]) == [1,2]
@test getindex.(Ref(g[:Hom]),[e1,e2]) == [2,2]

apex, ι₁, ι₂ = pushout(f, g);

@test argsof(ι₁(e1)) == NestedType(hs, [[1,2]])
@test argsof(ι₁(e3)) == NestedType(hs, [[2,3]])
@test ι₁(e3) == ι₁(e4) # these got merged together
@test argsof(ι₂(e1)) == NestedType(hs, [[2,3]])
@test ι₂(e3) != ι₂(e4) # These are not merged together
@test argsof(ι₂(e3)) == NestedType(hs, [[3,4]])


# ThCategory
############

walking_arrow = create_category([:a,:b], (f=(:a=>:b),))
c2 = create_category([:a,:b], (;))

f, g = homomorphisms(c2, walking_arrow; monic=true)
apex, ι₁, ι₂ = pushout(f,g);

@test is_natural(copair([f,g]))
@test is_natural(oplus([f,g]))

# The two non-identity compositions are left undefined: 
@test count(==(0),last.(collect(apex[:compose]))) == 2

end # module
