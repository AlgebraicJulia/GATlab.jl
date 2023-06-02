module TestEGraphs

using Test

using Gatlab

@theory ThMonoid <: ThEmpty begin
  default :: TYPE ⊣ []
  e ⊣ []
  (a * b) ⊣ [a, b]
  (a * b) * c == (a * (b * c)) ⊣ [a,b,c]
  a * e == a ⊣ [a]
  e * a == a ⊣ [a]
end

Γ = @context ThMonoid [a, b, c]

eg = EGraph(ThMonoid.T, Γ)

i1 = add!(eg, @term ThMonoid Γ (a * b))
i2 = add!(eg, @term ThMonoid Γ c)
merge!(eg, i1, i2)
rebuild!(eg)
i3 = add!(eg, @term ThMonoid Γ (c * c))
i4 = add!(eg, @term ThMonoid Γ (c * (a * b)))

@test i3 == i4

Γ = @context ThCategory [(x,y,z)::Ob, f::Hom(x,y), g::Hom(y,z)]

eg = EGraph(ThCategory.T, Γ)

i1 = add!(eg, @term ThCategory Γ (f ⋅ g))

@test_throws Exception add!(eg, @term ThCategory Γ (g ⋅ f))

merge!(eg, add!(eg, @term ThCategory Γ x), add!(eg, @term ThCategory Γ z))

i2 = add!(eg, @term ThCategory Γ (g ⋅ f))

end
