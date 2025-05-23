"""
Explicit Op model. Alternatively, see DerivedModels.jl (`OpFinSetC`) for 
theory-morphism-derived Op models.
"""

export OpC, op, CatWrapper


using ...Models
using ..StdTheories
using StructEquality

ThCategory.Meta.@wrapper CatWrapper 

@struct_hash_equal struct OpC{ObT, HomT}
  cat::CatWrapper
  OpC(c::CatWrapper) = new{impl_type.(Ref(c),[:Ob,:Hom])...}(c)
end

op(c::CatWrapper) = OpC(c)

using .ThCategory

rename(::Nothing, ::Dict{Symbol,Symbol}) = nothing
rename(nt::NamedTuple, d::Dict{Symbol,Symbol}) = 
  NamedTuple(get(d, k, k) => v for (k, v) in pairs(nt))


@instance ThCategory{ObT, HomT} [model::OpC{ObT, HomT}] where {ObT, HomT} begin
  Ob(x::ObT) = Ob(model.cat, x)
  Hom(x::HomT, d::ObT, cd::ObT) = Hom(model.cat, x, cd, d)
  id(x::ObT) = id(model.cat, x)
  dom(f::HomT; context) = 
    codom(model.cat, f; context=rename(context, Dict(:dom=>:codom, :codom=>:dom)))
  codom(f::HomT; context) = 
    dom(model.cat, f; context=rename(context, Dict(:dom=>:codom, :codom=>:dom)))
  compose(f::HomT, g::HomT; context=nothing) =
    compose(model.cat, g, f; 
            context=rename(context, Dict(:a=>:c, :c=>:a, :b=>:b)))
end
