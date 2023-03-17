module TestTheories 


using Revise
using Gatlab
using Test 

double = @theorymap ThNat -> ThNat begin
  ℕ => ℕ
  Z => Z
  S(n) => S(S(n))
end;

two = Trm(3, [Trm(3, [Trm(2)])])
@test double(two) == Trm(3,[Trm(3,[Trm(3,[Trm(3,[Trm(2)])])])])
to_int(trm) = count(==('3'), string(trm))           # to make Owen's eyes bleed
to_int′(trm) = count(==('S'), show_term(ThNat,trm)) # to slow the bleeding
@test to_int(two) == 2  
@test to_int(double(two)) == 4 
@test to_int′(double(two)) == 4

thin = @theorymap ThCategory -> ThPreorder begin
  Ob => Ob
  Hom(a,b) => Leq(a,b)
  (f ⋅ g) => trans(f, g)
  id(a) => refl(a)
end;

ctx = Context([[(Name(x),Typ(1)) for x in "αβγ"]...,
              (Name("f"),Typ(2,Trm.([8,9]))), (Name("g"),Typ(2,Trm.([9,10])))])
trm = Trm(3,Trm.([11,12]))
show_term(ThCategory, trm, ctx)

thin(trm)
show_ctx(ThPreorder,thin(ctx))
show_term(ThPreorder, thin(trm),thin(ctx))

end # module 
