using Revise
using Gatlab 

overlap = ThSet 

f = TheoryIncl(ThSet,ThGroup,[1])
g = TheoryIncl(ThSet,ThMonoid,[1])

prering = pushout(Name("PreRing"), f,g, rename_c=Dict{Int,Name}(2 => Name(:+), 4 => Name(Symbol("0"))))

prering[1]