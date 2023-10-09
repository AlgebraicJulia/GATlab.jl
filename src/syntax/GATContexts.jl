module GATContexts
export GATContext, @gatcontext

using ...Util
using ..Scopes, ..GATs
using StructEquality
using MLStyle
import ..ExprInterop: fromexpr, toexpr

"""
Parse, e.g.:

```
(a,b,c)::Ob
f::Hom(a, b)
g::Hom(b, c)
h::Hom(a, c)
h′::Hom(a, c)
compose(f, g) == h == h′
```
"""
function fromexpr(p::GATContext, e, ::Type{GATContext})
  e.head == :block || error("expected a block to parse into a GATContext, got: $e")
  newscope = fromexpr(p, e, TypeScope)
  GATContext(gettheory(p), ScopeList([allscopes(gettypecontext(p)); newscope]))
end

macro gatcontext(head, body)
  (parent, name) = @match head begin
    Expr(:call, name, mod) => (:($(GATContext)($(mod).Meta.theory)), name)
    Expr(:(<:), name, parent) => (parent, name)
    _ => error("invalid head for @gatcontext macro: $head")
  end

  esc(quote
    const $name = $(fromexpr)($parent, $(QuoteNode(body)), $(GATContext))
  end)
end

function Base.show(io::IO, p::GATContext)
  println(io, "GATContext(", nameof(p.theory), "):")
  for scope in allscopes(gettypecontext(p))
    for binding in scope
      println(io, "  ", toexpr(p, binding))
    end
  end
end

end # module 
