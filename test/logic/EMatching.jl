module TestEMatching

using Test

using Gatlab

Γ = @context ThCategory [(x,y,z)::Ob, f::Hom(x,y), g::Hom(x,x), h::Hom(y,y)]

eg = EGraph(ThCategory.T, Γ)

id = add!(eg, @term ThCategory Γ (f ⋅ id(y)))

compose_lvl = (@term ThCategory Γ (f ⋅ h)).head
id_lvl = (@term ThCategory Γ id(x)).head

instructions = [Scan(Reg(1)), Bind(compose_lvl, Reg(1), Reg(2)), Bind(id_lvl, Reg(3), Reg(4))]

m = Machine()

run!(m, eg, instructions, [Reg(4), Reg(2)])

@test m.matches[1] == [add!(eg, @term ThCategory Γ y), add!(eg, @term ThCategory Γ f)]

Γ′ = @context ThCategory [a::Ob, b::Ob, α::Hom(a,b)]
t = @term ThCategory Γ′ (α ⋅ id(b))
pat = Pattern(t, Γ′)
prog = compile(ThCategory.T, pat)

m = Machine()

push!(m.reg, id)
run!(m, eg, prog)

@test m.matches[1] == [add!(eg, @term ThCategory Γ y), add!(eg, @term ThCategory Γ f)]

end
