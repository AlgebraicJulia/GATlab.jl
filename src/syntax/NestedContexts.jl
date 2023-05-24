module NestedContexts
export NestedContext, DependentContext

using ..Theories
using ...Util.Names

struct NestedContext
  subcontexts::Vector{Pair{Name, Union{NestedContext, Typ}}}
  index_mapping::Vector{Int}
end

function Base.copy(c::NestedContext)
  NestedContext(
    copy(c.subcontexts),
    copy(c.index_mapping)
  )
end

function NestedContext()
  NestedContext(Pair{Name, Union{NestedContext, Typ}}[], Int[])
end

function Base.map(f::Function, c::NestedContext)
  NestedContext(
    map(c.subcontexts) do (name, ctx_or_typ)
      name => if typeof(ctx_or_typ) == Typ
        Typ(f(ctx_or_typ.head), ctx_or_typ.args)
      else
        map(f, ctx_or_typ)
      end
    end,
    c.index_mapping
  )
end

struct DependentContext
  args::NestedContext
  context::NestedContext
end

"""
We want to build up a dependent context by composing other dependent contexts together.

I.e. something like:

[dom::Arena, codom::Arena, f::Lens{dom, codom}]

To do this, we add each element one at a time.

# Arguments
- `xs::DependentContext`: the context to add an element to
- `x::DependentContext`: the new element
- `f::Vector{Lvl}`: a substitution from `sub.args` to `context.context + context.args`
"""
function Base.push!(xs::DependentContext, name::Name, x::DependentContext, f::Vector{Lvl})
  offset = length(xs.context.index_mapping)
  new_subcontext = map(x.context) do lvl
    if is_context(lvl)
      lvl + offset
    elseif is_argument(lvl)
      f[index(lvl)]
    else
      lvl
    end
  end
  push!(xs.context.subcontexts, name => new_subcontext)
  append!(xs.context.index_mapping,
          repeat([length(xs.context.subcontexts)], length(x.context.index_mapping)))
end

function Base.push!(xs::DependentContext, name::Name, x::Typ)
  push!(xs.context.subcontexts, name => x)
  push!(xs.context.index_mapping, length(xs.context.subcontexts))
end


"""
Next steps:

- Declare a struct from a nested context
- Typecheck that struct
- Reference that struct in other structs
- Use named nested contexts in theory maps


## Declaring structs

A struct declared from a nested context can either be declared

1. For a specific model of a theory
2. Generically

In the first case, the struct has no type parameters

In the second case, the struct has a type parameter for each type constructor in the theory
"""

end
