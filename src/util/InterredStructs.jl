module InterredStructs

using StructEquality

"""
This is used to construct Intrd values

We do not export ModuleKey, so there is no exported way to construct an Intrd
value except for `inter!`.
"""
struct ModuleKey
end

const module_key = ModuleKey()

"""
This represents an "interred" value.

The interred value stores a reference to the actual value because the actual
values are stored in a `WeakKeyDict`, and so thus can be garbage collected
when nothing points to them anymore. Thus, we need to keep around a reference

"""
@struct_hash_equal struct Intrd{T}
  hash::UInt64
  function Intrd{T}(id::UInt64, x::T) where {T}
    error("cannot construct Intrd directly; use inter!")
  end
  function Intrd{T}(id::UInt64, x::T, ::ModuleKey) where {T}
    new(id)
  end
end

struct Registry{T}
  lookup::Dict{Intrd{T}, T}
end

function inter!(registry::Registry{T}, x::T)::Intrd{T} where {T}
  h = hash(x)
  i = Intrd{T}(h, module_key)
  if i ∈ keys(registry.lookup)
    registry.lookup[i] == x || error("hash collision!")
  else
    registry.lookup[i] = x
  end
  i
end

function lookup(registry::Registry{T}, i::Intrd{T})::T where {T}
  registry.lookup[i]
end

end
