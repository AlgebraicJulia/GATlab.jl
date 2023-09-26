module TestGATs

using GATlab, Test
using .ThCategory

@withmodel GATC() (Ob, Hom, id, compose, dom, codom) begin

  codom(SwapMonoid) == dom(NatPlusMonoid)

  x = toexpr(compose(id(ThMonoid.THEORY), compose(SwapMonoid, NatPlusMonoid)))

  expected = @theorymap ThMonoid => ThNatPlus begin
    default => ℕ
    x ⋅ y ⊣ [x, y] => y + x
    e => Z
  end

  @test x == toexpr(expected)

end

end # module
