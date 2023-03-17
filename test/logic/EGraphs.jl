module TestEGraphs

using Test

using Gatlab

@theory Monoid <: ThEmpty begin
  U :: TYPE ⊣ []
  e :: U ⊣ []
  (a * b) :: U ⊣ [a::U, b::U]
  ((a * b) * c == (a * (b * c)) :: U) ⊣ [a::U, b::U, c::U]
  (a * e == a :: U) ⊣ [a::U]
  (e * a == a :: U) ⊣ [a::U]
end

@theory M <: Monoid begin
  a :: U ⊣ []
  b :: U ⊣ []
  c :: U ⊣ []
end

eg = EGraph(M)

println(@term M (a * b))
i1 = add!(eg, @term M (a * b))
println(@term M c)
i2 = add!(eg, @term M c)
merge!(eg, i1, i2)
rebuild!(eg)
i3 = add!(eg, @term M c * c)
i4 = add!(eg, @term M c * (a * b))

@test i3 == i4

@theory C <: ThCategory begin
  x :: Ob ⊣ []
  y :: Ob ⊣ []
  z :: Ob ⊣ []
  f :: Hom(x,y) ⊣ []
  g :: Hom(y,z) ⊣ []
end

eg = EGraph(C)

i1 = add!(eg, @term C (f ⋅ g))

@test_throws Exception add!(eg, @term C (g ⋅ f))

merge!(eg, add!(eg, @term C x), add!(eg, @term C z))

i2 = add!(eg, @term C (g ⋅ f))

end
