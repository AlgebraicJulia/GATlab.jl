module TestPresentations

using Gatlab
using Gatlab.Syntax.GATs: parsetypescope
using Test
T = ThCategory.THEORY

tscope = parsetypescope(
  T, 
  :([(a,b,c)::Ob, f::Hom(a,b), g::Hom(b,c), (h,h′)::Hom(a,c)]).args
)
_,_,_,f,g,h,h′ = idents(tscope)
h,h′ = AlgTerm.([h,h′])
fg = fromexpr(AppendScope(T, tscope), :(compose(f,g)), AlgTerm)
p1 = Presentation(T, tscope, [[fg, h]])
x1 = toexpr(p1)
p1′ = fromexpr(T,x1, Presentation);
@test length(only(p1′.eqs)) == 2

p2 = Presentation(T, tscope, [[fg, h, h′]])
x2 = toexpr(p2)
p2′ = fromexpr(T,x2, Presentation);
@test length(only(p2′.eqs)) == 3

# HasContext interface
@test nscopes(p1) == nscopes(T) + 1 
@test length(getscope(p1, nscopes(p1))) == 7
@test !hastag(p1, newscopetag())
@test hasname(p1, :f)
@test !hasname(p1, :q)
@test getlevel(p1, :id) < getlevel(p1, :f)
@test getlevel(p1, gettag(f)) == nscopes(p1)

end # module 