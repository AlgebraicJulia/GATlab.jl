module TestCombinatorial

using GATlab
using Test
using GATlab.Combinatorial.DataStructs: shape, subterms, validate, NMI, Nest, ScopedNMs
using GATlab.Combinatorial.CModels: enum,random_cardinalities
using GATlab.Combinatorial.Visualization: renderstr
using GATlab.NonStdlib.NonStdTheories: Th2Cat, ThTwoCat
using GATlab.Syntax.TheoryMaps: bind_localctx

# Unpack theory
T = Th2Cat.Meta.theory;
os, hs, h2s = sorts(T)

# Manually create a consistent cardinality assignment
m0, m1, m2, m3, m4 = NMI.(0:4)
sing(x::NMI)::NMI = NMI(Nest(reshape([x], 1, 1)))
h2mat = NMI[NMI(Nest([m3 m2; m1 m0])) NMI(reshape(NMI[], 0, 0)|>Nest, depth=1); 
            sing(m2)                  sing(m1)]
d = ScopedNMs(T, Dict(os => NMI(2), 
                      hs => NMI(Nest([m2 m0; m1 m1])), 
                      h2s => NMI(Nest(h2mat))))

@test sprint(show, MIME"text/plain"(), d[hs]) isa String # render as a table
@test renderstr(d[h2s]) isa String
# render(d[h2s]) # to visualize a nested matrix in html on a Mac

# Generate one automatically, fixing the Ob and Hom sets
gen_ds = random_cardinalities(T; init=Dict(os => NMI(2), hs => NMI(Nest([m2 m0; m1 m1]))))
# Shape of Hom2 is fixed by sizes of Ob and Hom sets
@test shape(d[h2s]) == shape(gen_ds[h2s])

m = CombinatorialModel(T; card_range=1:1) # terminal
@test validate(m)
m.sets[os] = ScopedNM(NMI(2), getcontext(T,os))
@test !validate(m)

# Modifying models
#-----------------
ntos = NestedType(os)
m = CombinatorialModel(T; init=deepcopy(d));
@test NestedTerm(3, ntos) == add_part!(m, ntos)
h11 = NestedType(hs, [CartesianIndex(1,1)])
m = CombinatorialModel(T; init=deepcopy(d));
add_part!(m, h11)

h2_h12 = NestedType(h2s, [CartesianIndex(1,2), CartesianIndex(3,2)])
@test getvalue.(subterms(T, h2_h12))==[1,2,3,2]

#########
# TWOCAT #
##########
# Unpack theory
T = ThTwoCat.Meta.theory;
os, hs, h2s = sorts(T)
idsort = AlgSort(termcons(T)[2]...)

m0, m1, m2, m3, m4 = NMI.(0:4)
rs(x, i, j, d=nothing) = NM(reshape(x, i, j); depth=d)
sing(x) = rs([x], 1, 1)

d = Dict(os => NMI(2), hs => NMI(Nest([m3 m0; m2 m1])))

d = random_cardinalities(T, 1:1; init=deepcopy(d));
ntos = NestedType(os)
            
m = CombinatorialModel(T; init=deepcopy(d));
add_part!(m, ntos)
rem_part!(m, NestedTerm(1,ntos))
@test last.(collect(m[idsort])) == [0, 1]

end # module
