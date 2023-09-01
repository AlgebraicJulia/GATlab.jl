module TestPresentations

using Gatlab
using Gatlab.Syntax.ExprInterop: parsetypescope
using Test
T = ThCategory.THEORY

tscope = parsetypescope(
  T, 
  :([(a,b,c)::Ob, f::Hom(a,b), g::Hom(b,c), (h,h′)::Hom(a,c)])
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

end # module 
