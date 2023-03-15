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

eg = EGraph()

i1 = add!(eg, @term M (a * b))
i2 = add!(eg, @term M c)
merge!(eg, i1, i2)
rebuild!(eg)
i3 = add!(eg, @term M c * c)
i4 = add!(eg, @term M c * (a * b))

@test i3 == i4

end
