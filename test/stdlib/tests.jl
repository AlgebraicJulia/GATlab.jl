module TestTheories 

using Gatlab
using Test 

double = @theorymap ThNat -> ThNat begin
  ℕ => ℕ
  Z => Z
  S(n) => S(S(n))
end;

l2,l3 = Lvl.([2,3])
two = Trm(l3, [Trm(l3, [Trm(l2)])])
@test double(two) == Trm(l3,[Trm(l3,[Trm(l3,[Trm(l3,[Trm(l2)])])])])
to_int(trm) = count(==('3'), string(trm))           # to make Owen's eyes bleed
to_int′(trm) = count(==('S'), string(show_term(ThNat,trm))) # to slow the bleeding
@test to_int(two) == 2  
@test to_int(double(two)) == 4 
@test to_int′(double(two)) == 4

@theory T1 <: ThEmpty begin 
  X::TYPE ⊣ []
  Y::TYPE ⊣ []
  Z::TYPE ⊣ []
  P(x, y)::X ⊣ [x::X,y::X]
  Q(u,w)::X ⊣ [u::Y,w::Z]
end
@theory T2 <: ThEmpty begin 
  XX::TYPE ⊣ []
  ϕ(i, o)::XX ⊣ [i::XX,o::XX]
  ψ(k)::XX ⊣ [k::XX]
end

tst = @theorymap T1 -> T2 begin
  X => XX 
  Y => XX
  Z => XX 
  P(e,r) =>  ϕ(ψ(r),e)
  Q(n,m) => ψ(m) 
end

trm = Trm(Lvl(4),[Trm(Lvl(1; context=true)), 
                  Trm(Lvl(5),Trm.(Lvl.([2,3]; context=true)))])
ctx = Context([(Name(x),Typ(Lvl(1))) for x in "abc"])
show_term(T1, trm, ctx)
@test tst(trm) == Trm(
  Lvl(2),
  [Trm(Lvl(3), 
      [Trm(Lvl(3), 
          [Trm(Lvl(3;context=true))])]), 
  Trm(Lvl(1; context=true))])


thin = @theorymap ThCategory -> ThPreorder begin
  Ob => Ob
  Hom(a,b) => Leq(a,b)
  (f ⋅ g) => trans(f, g)
  id(a) => refl(a)
end;

ctx = Context([[(Name(x),Typ(Lvl(1))) for x in "αβγ"]...,
              [(Name(n),Typ(Lvl(2),Trm.(Lvl.(is; context=true))))
                for (n,is) in [("f",[1,2]),("g",[2,3])]]...])
trm = Trm(Lvl(3),Trm.(Lvl.([4,5]; context=true)))
show_term(ThCategory, trm, ctx)

thin(trm)
show_ctx(ThPreorder, thin(ctx))
show_term(ThPreorder, thin(trm), thin(ctx))

end # module 
