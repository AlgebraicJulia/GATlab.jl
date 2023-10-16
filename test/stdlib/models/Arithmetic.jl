module TestArithmetic 

using GATlab
using Test

# Integers as model of naturals
#------------------------------
using .ThNatPlus

@withmodel IntNatPlus() (ℕ, Z, S, +) begin
  @test S(S(Z())) + Z() == 2
end

# IntMonoid = NatPlusMonoid(IntNatPlus)
#--------------------------------------
using .ThMonoid

@withmodel IntMonoid (e) begin
  @test e() == 0
  @test (ThMonoid.:(⋅)[IntMonoid])(3, 4) == 7
end

# Integers as preorder
#---------------------
using .ThPreorder

@withmodel IntPreorder() (Leq, refl, trans) begin
  @test trans((1,3), (3,5)) == (1,5)  
  @test_throws TypeCheckFail Leq((5,3), 5, 3)
  @test refl(2) == (2,2)
end

# Now using category interface

using .ThCategory

@withmodel IntPreorderCat (Hom, id, compose) begin
  @test compose((1,3), (3,5)) == (1,5)
  @test_throws TypeCheckFail Hom((5,3), 5, 3)
  @test_throws ErrorException compose((1,2), (3,5))
  @test id(2) == (2,2)
end

end # module 
