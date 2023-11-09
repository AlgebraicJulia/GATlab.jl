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

type_fg = EGraphs.extract(eg, EGraphs.etypeof(eg, i1); chooser=first)
@test type_fg == fromexpr(C, :(Hom(x,z)), AlgType)

@test_throws Exception add!(eg, :(g ⋅ f))

merge!(eg, add!(eg, :x), add!(eg, :z))

i2 = add!(eg, :(g ⋅ f))

# E-Matching
############

@gatcontext C(ThCategory) begin
  x::Ob
  y::Ob
  z::Ob
  f::Hom(x,y)
  g::Hom(x,x)
  h::Hom(y,y)
end

eg = EGraph(C)

id = add!(eg, :(f ⋅ id(y)))

compose_method = fromexpr(C, :(f ⋅ h), AlgTerm).body.method
id_method = fromexpr(C, :(id(x)), AlgTerm).body.method

instructions = [Scan(Reg(1)), Bind(compose_method, Reg(1), Reg(2)), Bind(id_method, Reg(3), Reg(4))]

m = Machine()

run!(m, eg, instructions, [Reg(4), Reg(2)])

@test m.matches[1] == [add!(eg, :y), add!(eg, :f)]

# Γ = @context ThCategory [a::Ob, b::Ob, α::Hom(a,b)]
# t = @term ThCategory Γ (α ⋅ id(b))
# pat = Pattern(t, Γ)
# prog = compile(ThCategory.T, pat)

# m = Machine()

# push!(m.reg, id)
# run!(m, eg, prog)

# @test m.matches[1] == [add!(eg, @term C y), add!(eg, @term C f)]

end # module 
