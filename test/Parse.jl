module ParseTests

using Gatlab

@theory ThSet <: ThEmpty begin
  Ob::TYPE ⊣ []
end

@theory ThGraph <: ThSet begin
  Hom(a,b)::TYPE ⊣ [(a::Ob, b::Ob)]
end

@theory ThLawlessCat <: ThGraph begin
  (f ⋅ g)::Hom(a,c) ⊣ [(a::Ob, b::Ob, c::Ob), (f::Hom(a,b), g::Hom(b,c))]
  id(a)::Hom(a,a) ⊣ [(a::Ob,)]
end

@theory Category <: ThLawlessCat begin
  ((f ⋅ g) ⋅ h == (f ⋅ (g ⋅ h)) :: Hom(a,d)) ⊣ [(a::Ob, b::Ob, c::Ob, d::Ob), (f::Hom(a,b), g::Hom(b,c), h::Hom(c,d))]
  (id(a) ⋅ f == f :: Hom(a,b)) ⊣ [(a::Ob, b::Ob), (f::Hom(a,b),)]
  (f ⋅ id(b) == f :: Hom(a,b)) ⊣ [(a::Ob, b::Ob), (f::Hom(a,b),)]
end

end
