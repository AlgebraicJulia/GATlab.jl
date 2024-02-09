@theory Th2Cat <: ThCategory begin
  Hom2(dom::(a→b), codom::(a→b))::TYPE ⊣ [a::Ob, b::Ob]
  dummy(x::(a→b),y::(a→b),F::Hom2(x,y))::Hom2(y, x) ⊣ [(a,b)::Ob]
end

@theory ThTwoCat <: ThCategory begin
  Hom2(fwd::(a→b), rev::(b→a))::TYPE ⊣ [a::Ob, b::Ob]
  dummy(x::(a→b),y::(b→a),F::Hom2(x,y))::Hom2(y, x) ⊣ [(a,b)::Ob]
end