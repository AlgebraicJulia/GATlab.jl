module Presentations 
export Presentation, getscope
using ..Scopes, ..GATs
using StructEquality 

"""
A presentation has a set of generators, given by a `TypeScope`, and a set of 
equations among terms which can refer to those generators. Each element of 
`eqs` is a list of terms which are asserted to be equal.
"""
@struct_hash_equal struct Presentation
  theory::GAT
  scope::TypeScope
  eqs::Vector{Vector{AlgTerm}}
  function Presentation(g, s, eqs=[])
    gs = AppendScope(g, s)
    # scope terms must be defined in GAT 
    sortcheck.(Ref(gs), getvalue.(s))
    # eq terms must be defined in GAT ++ scope
    for eq in eqs 
      length(eq) > 1 || error("At least two things must be equated")
      sortcheck.(Ref(gs), eq)
    end
    new(g, s, collect.(eqs))
  end
end

getscope(p::Presentation) = AppendScope(p.theory, p.scope)

end # module 
