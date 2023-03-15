module TestLists

using Gatlab.Lists
using Test

l1 = Bwd{Int}()

@test length(l1) == 0

l2 = Bwd(l1, 2)

@test length(l2) == 1
@test l2[end] == 2

l3 = Bwd([2,3,3,1])

@test length(l3) == 4
@test l3[3] == 3

@test_throws BoundsError l3[5]

l1 = Fwd{Int}()

@test length(l1) == 0

l2 = Fwd(2, l1)

@test length(l2) == 1
@test l2[1] == 2

l3 = Fwd([2,3,3,1])

@test length(l3) == 4
@test l3[3] == 3

@test_throws BoundsError l3[5]

@test Fwd(Bwd(l3)) == l3

@test [l3...] == [Bwd(l3)...] == [2,3,3,1]

@test vcat(l3, l2) == Fwd([2,3,3,1,2])

@test vcat(Bwd(l3), Bwd(l2)) == Bwd([2,3,3,1,2])

end
