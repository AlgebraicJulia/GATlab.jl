module Rename

using ..GATs
using ..Scopes
import ..Scopes: rename

export rename

# rename methods are already defined in gats

function rename(renames::Dict{Symbol,Symbol}, name::Union{Nothing,Symbol})
  # @info "naming" name ∈ keys(renames)
  name ∈ keys(renames) ? renames[name] : name
end

## accessors OrderedDict{Ident, Dict{Int, Ident}}
## do we need to rename axioms::Vector{Ident}
# function rename(gat::GAT, renames::Dict{Symbol,Symbol}=Dict{Symbol,Symbol}())
#   GAT(gat.name, rename(gat.segments, rename), gat.resolvers, rename(gat.sorts, rename), gat.accessors, gat.axioms) 
# end

# function rename(resolvers::OrderedDict{Ident, MethodResolver}, renames::Dict{Symbol,Symbol}=Dict{Symbol,Symbol}())
#   if length(resolvers) == 0
#     resolvers
#   else 
#     merge(map(collect(resolvers)) do (r, m)
#       Dict(rename(r, renames) => rename(m, renames))
#     end...)
#   end
# end

# gat.jl
# function rename(m::MethodResolver, renames::Dict{Symbol,Symbol}=Dict{Symbol,Symbol}())
#   MethodResolver(rename(m.bysignature, renames))
# end


function rename(scopes::Vector{HasScope{T}}, renames::Dict{Symbol,Symbol}=Dict{Symbol,Symbol}()) where {T}
  map(scopes) do scope
    GATSegment(rename(scope.scope, renames))
  end
end

# appears in sk.scope.names :: Dict{Symbol, LID}
function rename(names::Union{Dict{Symbol, LID}, Dict{Symbol, Int}}, renames::Dict{Symbol,Symbol}=Dict{Symbol,Symbol}())
  if length(names) == 0
    names
  else 
    merge(map(collect(names)) do (name, v)
      Dict(rename(name, renames) => v)
    end...)
  end
end


end
