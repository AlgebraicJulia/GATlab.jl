module TestGATs

using GATlab, Test

using .ThCategory

# Uh-oh! This segfaults when inside the @withmodel
expected = @theorymap ThMonoid => ThNatPlus begin
  default => ℕ
  x ⋅ y ⊣ [x, y] => y + x
  e() => Z()
end

@withmodel GATC() (Ob, Hom, id, compose, dom, codom) begin

  codom(SwapMonoid.MAP) == dom(NatPlusMonoid.MAP)

  x = toexpr(compose(id(ThMonoid.THEORY), compose(SwapMonoid.MAP, NatPlusMonoid.MAP)))

  @test x == toexpr(expected.MAP)

end

end # module
