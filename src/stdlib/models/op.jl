"""
Explicit Op model. Alternatively, see DerivedModels.jl (`OpFinSetC`) for 
theory-morphism-derived Op models.
"""

export OpC, op


using ...Models
using ..StdTheories
using StructEquality

# TODO when we implement custom structs for models of a particular theory, we 
# can use that rather than a generic "C" for which we then have to check 
# whether it implements the theory.

@struct_hash_equal struct OpC{ObT, HomT, C}
  cat::C 
  function OpC(c::C) where C 
    obtype = impl_type(c, ThCategory, :Ob)
    homtype = impl_type(c, ThCategory, :Hom)
    implements(c, ThCategory) ? new{obtype, homtype, C}(c) : error("bad")
  end
end

op(c) = OpC(c)

using .ThCategory

rename(::Nothing, ::Dict{Symbol,Symbol}) = nothing
rename(nt::NamedTuple, d::Dict{Symbol,Symbol}) = 
  NamedTuple(get(d, k, k) => v for (k, v) in pairs(nt))


@instance ThCategory{ObT, HomT} [model::OpC{ObT, HomT, C}] where {ObT, HomT, C} begin
  Ob(x::ObT) = Ob[model.cat](x)
  Hom(x::HomT, d::ObT, cd::ObT) = Hom[model.cat](x, cd, d)
  id(x::ObT) = id[model.cat](x)
  dom(f::HomT; context) = 
    codom[model.cat](f; context=rename(context, Dict(:dom=>:codom, :codom=>:dom)))
  codom(f::HomT; context) = 
    dom[model.cat](f; context=rename(context, Dict(:dom=>:codom, :codom=>:dom)))
  compose(f::HomT, g::HomT; context=nothing) =
    compose[model.cat](g, f; 
            context=rename(context, Dict(:a=>:c, :c=>:a, :b=>:b)))
end
