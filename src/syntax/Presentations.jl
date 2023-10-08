module Presentations
export Presentation, @present

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
function fromexpr(p::Presentation, e, ::Type{Presentation})
  e.head == :block || error("expected a block to parse into a Presentation, got: $e")
  newscope = fromexpr(p, e, TypeScope)
  Presentation(gettheory(p), ScopeList([allscopes(gettypecontext(p)); newscope]))
end

macro present(head, body)
  (parent, name) = @match head begin
    Expr(:call, name, mod) => (:($(Presentation)($(mod).THEORY)), name)
    Expr(:(<:), name, parent) => (parent, name)
    _ => error("invalid head for @present macro: $head")
  end

  esc(quote
    const $name = $(fromexpr)($parent, $(QuoteNode(body)), $(Presentation))
  end)
end

function Base.show(io::IO, p::Presentation)
  println(io, "Presentation(", nameof(p.theory), "):")
  for scope in allscopes(gettypecontext(p))
    for binding in scope
      println(io, "  ", toexpr(p, binding))
    end
  end
end

end # module 
