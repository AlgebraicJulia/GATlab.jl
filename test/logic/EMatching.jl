module TestEMatching

using Test

using Gatlab

@theory C <: ThCategory begin
  x::Ob
  y::Ob
  z::Ob
  f::Hom(x,y)
  g::Hom(x,x)
  h::Hom(y,y)
end

eg = EGraph(C.T)

id = add!(eg, @term C (f ⋅ id(y)))

compose_lvl = (@term C (f ⋅ h)).head
id_lvl = (@term C id(x)).head

instructions = [Scan(Reg(1)), Bind(compose_lvl, Reg(1), Reg(2)), Bind(id_lvl, Reg(3), Reg(4))]

m = Machine()

run!(m, eg, instructions, [Reg(4), Reg(2)])

@test m.matches[1] == [add!(eg, @term C y), add!(eg, @term C f)]

Γ = @context ThCategory [a::Ob, b::Ob, α::Hom(a,b)]
t = @term ThCategory Γ (α ⋅ id(b))
pat = Pattern(t, Γ)
prog = compile(ThCategory.T, pat)

m = Machine()

push!(m.reg, id)
run!(m, eg, prog)

@test m.matches[1] == [add!(eg, @term C y), add!(eg, @term C f)]

end
