module TestArithmetic 

using GATlab
using Test

using .ThNatPlus

@withmodel IntNatPlus() (ℕ, Z, S, +) begin
  @test S(S(Z())) + Z() == 2
end


end # module 
