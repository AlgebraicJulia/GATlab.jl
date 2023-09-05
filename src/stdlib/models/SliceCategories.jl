module SliceCategories
export SliceC, SliceOb

using ....Models
using ...StdTheories

struct SliceOb{ObT, HomT}
  ob::ObT
  hom::HomT
end

struct SliceC{ObT, HomT, C<:Model{Tuple{ObT, HomT}}} <: Model{Tuple{SliceOb{ObT, HomT}, HomT}}
  cat::C
  over::ObT
end

using .ThCategory

@instance ThCategory{SliceOb{ObT, HomT}, HomT} (;model::SliceC{ObT, HomT, C}) where {ObT, HomT, C} begin
  Ob(x::SliceOb{ObT, HomT}) =
    Ob(x.ob; model=model.cat) && Hom(x.hom, x.ob, model.over; model=model.cat)

  Hom(f::HomT, x::SliceOb{ObT, HomT}, y::SliceOb{ObT, HomT}) =
    Hom(f, x.ob, y.ob; model=model.cat) &&
    compose(f, y.hom; model=model.cat, context=(a=x.ob, b=y.ob, c=model.over)) == x.hom

  id(x::SliceOb{ObT, HomT}) = id(x.ob; model=model.cat)

  compose(f::HomT, g::HomT; context=nothing) =
    compose(f, g; model=model.cat, context=isnothing(context) ? nothing : map(x -> x.ob, context))
end

end
