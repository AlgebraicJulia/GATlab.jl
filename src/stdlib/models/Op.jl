module Op 

export OpC, op


using ....Models
using ...StdTheories
using StructEquality


@struct_hash_equal struct OpC{ObT, HomT, C<:Model{Tuple{ObT, HomT}}} <: Model{Tuple{ObT, HomT}}
  cat::C
end

op(c) = OpC(c)

using .ThCategory

rename(::Nothing, ::Dict{Symbol,Symbol}) = nothing
rename(nt::NamedTuple, d::Dict{Symbol,Symbol}) = 
  NamedTuple(Dict([get(d, k, k) => v for (k, v) in pairs(nt)]))


@instance ThCategory{ObT, HomT} (;model::OpC{ObT, HomT, C}) where {ObT, HomT, C} begin
  Ob(x::ObT) = Ob(x; model=model.cat)
  Hom(x::HomT, d::ObT, cd::ObT) = Hom(x, cd, d; model=model.cat)
  id(x::ObT) = id(x; model=model.cat)
  dom(f::HomT; context) = codom(f; model=model.cat, context)
  codom(f::HomT; context) = dom(f; model=model.cat, context)
  compose(f::HomT, g::HomT; context=nothing) =
    compose(g, f; model=model.cat, 
            context=rename(context, Dict(:a=>:c, :c=>:a, :b=>:b)))
end

end # module 
