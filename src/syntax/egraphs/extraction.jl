struct Input
  eid::EId
end

const CompMethod = Union{Input, MethodApp{EId}, EConstant}

"""
Naive greedy algorithm for extracting some method of
computing each of the eids in `target` given values
for the eids in `given`.
"""
function extract(
  target::AbstractSet{EId},
  given::AbstractSet{EId},
  egraph::EGraph
)::Union{Nothing, Dict{EId, InputOrApp}}
  computed = Dict{EId, InputOrApp}(i => Input(i) for i in given)
  """
  Returns true if `id` can be computed from `given`, false otherwise
  """
  function extract!(id::EId)
    if id in keys(computed)
      return true
    end
    methods = CompMethod[]
    for eterm in egraph.eclasses[id].reps
      if eterm.body isa Ident
        continue
      elseif eterm.body isa EConstant
        computed[id] = eterm.body
        return true
      else
        if all(extract!, eterm.body.args)
          computed[id] = eterm.body
          return true
        end
      end
    end
    return false
  end

  success = all(extract!, target)

  if success
    computed
  else
    nothing
  end
end


