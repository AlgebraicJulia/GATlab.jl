module TestPresentations

using GATlab
using Test
T = ThCategory.THEORY
ctx = Presentation(T)
tscope = fromexpr(
  ctx, 
  :([(a,b,c)::Ob, f::Hom(a,b), g::Hom(b,c), (h,h′)::Hom(a,c), f⋅g == h, h == h′]),
  TypeScope
)
p1 = Presentation(T, tscope)

# HasContext interface
@test nscopes(p1) == nscopes(T) + 1 
@test length(getscope(p1, nscopes(p1))) == 9
@test !hastag(p1, newscopetag())
@test hasname(p1, :f)
@test !hasname(p1, :q)
@test getlevel(p1, :id) < getlevel(p1, :f)

@present SchGraph(ThCategory) begin
  (E,V)::Ob
  src::Hom(E,V)
  tgt::Hom(E,V)
end

src, tgt = idents(SchGraph; name=[:src, :tgt])
Hom = ident(SchGraph; name=:Hom)

@test getvalue(SchGraph[src]).body.head == Hom

@present SchFiberedGraph <: SchGraph begin
  (FE, FV)::Ob
  fsrc::(FE → FV)
  ftgt::(FE → FV)
  v::(FV → V)
  e::(FE → E)
  fsrc ⋅ v == e ⋅ src
  ftgt ⋅ v == e ⋅ tgt
end

@test nscopes(gettypecontext(SchFiberedGraph)) == 2

@present Z(ThGroup) begin
  (a,)
end

t = fromexpr(Z, :(i(a) ⋅ (2::default)), AlgTerm)
a = ident(Z; name=:a)

@test compile(Dict(a => :a), t; theorymodule=ThGroup) == :($(ThGroup).:(⋅)($(ThGroup).i(a), 2))

@present D₄(ThGroup) begin
  (r,f) :: default

  (f⋅f) == e() 
  (r⋅r⋅r⋅r) == e()
end

end # module 
