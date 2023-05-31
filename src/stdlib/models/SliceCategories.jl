module SliceCategories
export SliceC, SliceOb

using ....Models
using ....Dsl
using ...StdTheories

struct SliceOb{Ob, Hom}
  ob::Ob
  hom::Hom
end

@model ThCategory{SliceOb{Ob, Hom}, Hom} (self::SliceC{Ob, Hom, C<:Model{ThCategory.T, Tuple{Ob, Hom}}}) begin
  cat::C
  over::Ob

  Ob(x::SliceOb{Ob, Hom}) =
    checkvalidity(self.cat, ThCategory.Ob(), x.ob) &&
    checkvalidity(self.cat, ThCategory.Hom(), x.ob, self.over, x.hom)

  Hom(x::SliceOb{Ob, Hom}, y::SliceOb{Ob, Hom}, f::Hom) =
    checkvalidity(self.cat, ThCategory.Hom(), x.ob, y.ob, f) &&
    ap(self.cat, ThCategory.:(⋅)(), x.ob, y.ob, self.over, f, y.hom) == x.hom

  id(x::SliceOb{Ob, Hom}) = ap(self.cat, ThCategory.id(), x.ob)

  ⋅(x, y, z, f, g) = ap(self.cat, ThCategory.:(⋅)(), x.ob, y.ob, z.ob, f, g)
end

end
