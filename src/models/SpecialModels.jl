module SpecialModels
export Dispatch, InitialModel, TerminalModel, InitialModel′, TerminalModel′

using ...Syntax: Ident, GAT, AlgSort, hastag, methodof, ident
using ...Syntax.TheoryInterface: Dispatch, InitialModel′, TerminalModel′
import ...Syntax.TheoryInterface: implements, impl_type 
import ..ModelInterface: _implements


# Public constants
##################
""" The unique term of type `InitialModel′` """
const InitialModel = InitialModel′()

""" The unique term of type `TerminalModel′` """
const TerminalModel = TerminalModel′()

# Accessing Dispatch
####################

Base.haskey(d::Dispatch, k::AlgSort) = haskey(d.jltypes, k) 

Base.getindex(d::Dispatch, a::AlgSort)::Type = d.jltypes[a]

function Base.getindex(d::Dispatch, x::Ident)::Type
  for (k, v) in d.jltypes
    methodof(k) == x && return v
  end
  throw(KeyError(x))
end

# Implements
#############

function implements(::Dispatch, theory_mod::Module, name::Symbol, types=nothing) 
  if isnothing(types)
    !isempty(methods(getfield(theory_mod, name))) # there exists *some* method
  else 
    hasmethod(getfield(theory_mod, name), types) # must be methods with these types
  end
end 

function _implements(::Dispatch, theory::Module, name::Symbol, types::Vector{<:Type}) 
  f = getfield(theory, name)
  any(==(Union{}), types) && return true # no such methods (Julia 1.10 bug)
  hasmethod(f, Tuple{types...})
end

function implements(::InitialModel′, ::Module, ::Symbol, types=nothing) 
  isnothing(types) || all(==(Union{}), types)
end

_implements(::InitialModel′, ::Module, ::Symbol, types::Vector{<:Type}) =
  all(==(Union{}), types)

function implements(::TerminalModel′, ::Module, ::Symbol, types=nothing) 
  isnothing(types) || all(==(Nothing), types)
end

_implements(::TerminalModel′, ::Module, ::Symbol, types::Vector{<:Type}) =
  all(==(Nothing), types)


# Impl Type
###########

function impl_type(m::Dispatch, mod::Module, name::Symbol)
  x = ident(mod.Meta.theory; name)
  impl_type(m, last(only(mod.Meta.theory.resolvers[x])))
end

impl_type(d::Dispatch, x::Ident) = d[x]


impl_type(::InitialModel′, ::Ident) = Union{}

impl_type(::TerminalModel′, ::Ident) = Nothing


end # module
