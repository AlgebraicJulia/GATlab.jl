module SliceCategories
export SliceC, SliceOb

using ....Models
using ...StdTheories

struct SliceOb{Ob, Hom}
  ob::Ob
  hom::Hom
end

struct SliceC{Ob, Hom, C<:Model{Tuple{Ob, Hom}}} <: Model{SliceOb{Ob, Hom}, Hom}
  cat::C
  over::Ob
end

using .ThCategory

@instance ThCategory{SliceOb{Ob, Hom}, Hom} (;model::SliceC{Ob, Hom, C}) where {Ob, Hom, C} begin
  Ob(x::SliceOb{Ob, Hom}) =
    Ob(x.ob; model=model.cat) && Hom(x.hom, x.ob, self.over; model=model.cat)

  Hom(f::Hom, x::SliceOb{Ob, Hom}, y::SliceOb{Ob, Hom}) =
    Hom(f, x.ob, y.ob; model=model.cat) &&
    compose(f, y.hom; model=model.cat, context=(a=x.ob, b=y.ob, c=model.over)) == x.hom

  id(x::SliceOb{Ob, Hom}) = id(x.ob; model=model.cat)

  compose(f, g; context=nothing) =
    compose(f, g; model=model.cat, context=isnothing(context) ? nothing : map(x -> x.ob, context))
end

end
