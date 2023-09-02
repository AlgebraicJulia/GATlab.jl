module ExprInterop
export toexpr, fromexpr

using ..Scopes
using ...Util.MetaUtils
using MLStyle 

"""
`toexpr(c::Context, t) -> Any`

Converts Gatlab syntax into an Expr that can be read in via `fromexpr` to get
the same thing. Crucially, the output of this will depend on the order of the
scopes in `c`, and if read back in with a different `c` may end up with
different results.
"""
function toexpr end

"""
`fromexpr(c::Context, e::Any, T::Type) -> Union{T,Nothing}`

Converts a Julia Expr into type T, in a certain scope.
"""
function fromexpr end

function toexpr(c::Context, x::Ident)
  if !hasident(c, x)
    return x
  end
  tag_level = getlevel(c, gettag(x))
  if isnamed(x)
    if tag_level == getlevel(c, nameof(x))
      nameof(x)
    else
      Symbol(nameof(x), "!", tag_level)
    end
  else
    if tag_level == nscopes(c)
      Symbol(sprint(show, x; context=:color=>false))
    else
      Symbol(sprint(show, x; context=:color=>false), "!", tag_level)
    end
  end
end

const explicit_level_regex = r"^(.*)!(\d+)$"
const unnamed_var_regex = r"^#(\d+)$"

function fromexpr(c::Context, e, ::Type{Ident}; sig=nothing)
  e isa Ident && return e
  e isa Symbol || error("expected a Symbol, got: $e")
  s = string(e)
  m = match(explicit_level_regex, s)
  if !isnothing(m)
    scope = getscope(c, parse(Int, m[2]))
    m2 = match(unnamed_var_regex, m[1])
    if !isnothing(m2)
      ident(scope; lid=LID(parse(Int, m2[1])), sig)
    else
      ident(scope; name=Symbol(m[1]), sig)
    end
  else
    m2 = match(unnamed_var_regex, s)
    if !isnothing(m2)
      ident(c; lid=LID(parse(Int, m2[1])), sig, level=nscopes(c))
    else
      ident(c; name=e, sig)
    end
  end
end

function toexpr(c::Context, ref::Reference)
  if isnothing(rest(ref))
    toexpr(c, first(ref))
  else
    error("paths not supported yet")
  end
end

function fromexpr(c::Context, e, ::Type{Reference}; sig=nothing)
  e isa Symbol || error("paths not supported yet")
  Reference(fromexpr(c, e, Ident; sig))
end

end # module
