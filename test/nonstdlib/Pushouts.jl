
using Test, GATlab, GATlab.Stdlib, GATlab.NonStdlib

using .ThPushout

T = ThPushout.Meta.theory
@test all(e -> e isa Expr, toexpr.(Ref(T), T.segments))

"""
Pushout Input                       Output
   1  <--- a ---> x                   12x
   2  <--- b ---↗                     3y
   3  <--- c ---> y                   4
   4              z                   z

Universal input:                    Output
  1 --↘ d                          12x -> c 
  2 --> c <-- x                     3y -> b
  3 --> b <-- y                      4 -> b
  4 --↗ a <-- z                      z -> a
"""

@withmodel FinSetC() (pushout, universal, cospan, ι₁) begin
  res = pushout(Span(3, [1,2,3], [1,1,2]); context=(d=4, c=3))
  @test res == PushoutInt(4, [1,1,2,3],[1,2,4])
  @test cospan(res) == Cospan(4, [1,1,2,3], [1,2,4])
  @test ι₁(res) == [1,1,2,3]
  @test universal(res, Cospan(4, [3,3,2,2],[3,2,1])) == [3,2,2,1]
  @test_throws ErrorException universal(PushoutInt(4, [1,1,2,3],[1,2,3]), Cospan(4, [3,3,2,2],[3,2,1]))
end
