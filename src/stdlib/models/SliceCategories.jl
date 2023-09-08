module SliceCategories
export SliceC, SliceOb

using ....Models
using ...StdTheories
using StructEquality

@struct_hash_equal struct SliceOb{ObT, HomT}
  ob::ObT
  hom::HomT
end

@struct_hash_equal struct SliceC{ObT, HomT, C<:Model{Tuple{ObT, HomT}}} <: Model{Tuple{SliceOb{ObT, HomT}, HomT}}
  cat::C
  over::ObT
end

using .ThCategory

@instance ThCategory{SliceOb{ObT, HomT}, HomT} (;model::SliceC{ObT, HomT, C}) where {ObT, HomT, C} begin
  function Ob(x::SliceOb{ObT, HomT})
    try
      Ob(x.ob; model=model.cat)
    catch e
      @fail ("ob is not valid", e)
    end
    try
      Hom(x.hom, x.ob, model.over; model=model.cat)
    catch e
      @fail ("hom is not valid", e)
    end
    x
  end

  # Ob(ob::ObT, hom::HomT) = Ob(SliceOb{ObT, HomT}(ob, hom))

  function Hom(f::HomT, x::SliceOb{ObT, HomT}, y::SliceOb{ObT, HomT})
    try
      Hom(f, x.ob, y.ob; model=model.cat)
    catch e
      @fail ("morphism is not valid in base category", e)
    end
    compose(f, y.hom; model=model.cat, context=(a=x.ob, b=y.ob, c=model.over)) == x.hom ||
      @fail "commutativity of triangle does not hold"
    f
  end

  id(x::SliceOb{ObT, HomT}) = id(x.ob; model=model.cat)

  compose(f::HomT, g::HomT; context=nothing) =
    compose(f, g; model=model.cat, context=isnothing(context) ? nothing : map(x -> x.ob, context))
end

end
