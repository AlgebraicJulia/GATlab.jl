module TestEGraphs

using Test

using GATlab

@gatcontext P(ThMonoid) begin
  (a,b,c)
end

eg = EGraph(P)

i1 = add!(eg, :(a ⋅ b))
i2 = add!(eg, :c)
merge!(eg, i1, i2)
rebuild!(eg)
i3 = add!(eg, :(c ⋅ c))
i4 = add!(eg, :(c ⋅ (a ⋅ b)))

@test i3 == i4

@gatcontext C(ThCategory) begin
  (x,y,z) :: Ob
  f :: Hom(x,y)
  g :: Hom(y,z)
end

eg = EGraph(C)

i1 = add!(eg, :(f ⋅ g))

EGraphs.etypeof(eg, i1)

EGraphs.extract(eg, EGraphs.etypeof(eg, i1); chooser=first)

@test_throws Exception add!(eg, :(g ⋅ f))

merge!(eg, add!(eg, :x), add!(eg, :z))

i2 = add!(eg, :(g ⋅ f))

# E-Matching
############

# @theory C <: ThCategory begin
#   x::Ob
#   y::Ob
#   z::Ob
#   f::Hom(x,y)
#   g::Hom(x,x)
#   h::Hom(y,y)
# end

# eg = EGraph(C.T)

# id = add!(eg, @term C (f ⋅ id(y)))

# compose_lvl = (@term C (f ⋅ h)).head
# id_lvl = (@term C id(x)).head

# instructions = [Scan(Reg(1)), Bind(compose_lvl, Reg(1), Reg(2)), Bind(id_lvl, Reg(3), Reg(4))]

# m = Machine()

# run!(m, eg, instructions, [Reg(4), Reg(2)])

# @test m.matches[1] == [add!(eg, @term C y), add!(eg, @term C f)]

# Γ = @context ThCategory [a::Ob, b::Ob, α::Hom(a,b)]
# t = @term ThCategory Γ (α ⋅ id(b))
# pat = Pattern(t, Γ)
# prog = compile(ThCategory.T, pat)

# m = Machine()

# push!(m.reg, id)
# run!(m, eg, prog)

# @test m.matches[1] == [add!(eg, @term C y), add!(eg, @term C f)]

end # module 
