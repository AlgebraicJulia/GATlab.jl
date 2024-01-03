export SliceC, SliceOb

using ...Models
using ..StdTheories
using StructEquality

@struct_hash_equal struct SliceOb{ObT, HomT}
  ob::ObT
  hom::HomT
end

@struct_hash_equal struct SliceC{ObT, HomT, C<:Model{Tuple{ObT, HomT}}} <: Model{Tuple{SliceOb{ObT, HomT}, HomT}}
  cat::C
  over::ObT
  # function SliceC(cat, over)
  #   implements(cat, ThCategory)
  #   new(cat, Ob[cat](over))
  # end
end

using .ThCategory

@instance ThCategory{SliceOb{ObT, HomT}, HomT} [model::SliceC{ObT, HomT, C}] where {ObT, HomT, C} begin
  function Ob(x::SliceOb{ObT, HomT})
    try
      Ob[model.cat](x.ob)
    catch e
      @fail ("ob is not valid", e)
    end
    try
      Hom[model.cat](x.hom, x.ob, model.over)
    catch e
      @fail ("hom is not valid", e)
    end
    x
  end

  # Ob(ob::ObT, hom::HomT) = Ob(SliceOb{ObT, HomT}(ob, hom))

  function Hom(f::HomT, x::SliceOb{ObT, HomT}, y::SliceOb{ObT, HomT})
    try
      Hom[model.cat](f, x.ob, y.ob)
    catch e
      @fail ("morphism is not valid in base category", e)
    end
    compose[model.cat](f, y.hom; context=(a=x.ob, b=y.ob, c=model.over)) == x.hom ||
      @fail "commutativity of triangle does not hold"
    f
  end

  id(x::SliceOb{ObT, HomT}) = id[model.cat](x.ob)

  compose(f::HomT, g::HomT; context=nothing) =
    compose[model.cat](f, g; context=isnothing(context) ? nothing : map(x -> x.ob, context))
end
