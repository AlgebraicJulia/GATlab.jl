module Lenses

using ....Syntax
using ....Models
using ...StdTheories

struct SimpleArena{T<:AbstractTheory}
  pos::Context
  dir::Context
end

"""
expose is a Kleisli map from codom.pos to dom.pos
update is a Kleisli map from dom.dir to dom.pos + codom.dir
"""
struct SimpleKleisliLens{T<:AbstractTheory}
  dom::SimpleArena{T}
  codom::SimpleArena{T}
  expose::Vector{Trm}
  update::Vector{Trm}
end

struct SimpleKleisliLensC{T<:AbstractTheory} <: Model{ThStrictMonCat}
end

module SimpleKleisliLensImpl

"""
l₁ = (f, f#)
l₂ = (g, g#)

l = l₁ ⋅ l₂

l = (h, h#)

   f#    g#
B <-- D <-- F
   f     g
A --> C --> E

f : C -> A
g : E -> B

f# : B -> A + D
g# : D -> C + F

h = g ⋅ f

        f#        1_A+g#             1_A + f + 1_F              ∇_A + 1_F
h# = B --> A + D -------> A + C + F ---------------> A + A + F -----------> A + F
"""
function compose(l₁::SimpleKleisliLens{T}, l₂::SimpleKleisliLens{T}) where {T <: AbstractTheory}
  expose = substitute_all(l₁.expose, l₂.expose)
  update = substitute_all(
    l₁.update,
    coproduct(id(l₁.dom.pos), l₂.update),
    coproduct(id(l₁.dom.pos), l₁.expose, id(l₂.codom.dir)),
    coproduct(collapse(l₁.dom.pos), id(l₂.codom.dir))
  )
  SimpleKleisliLens{T}(
    l₁.dom,
    l₂.codom,
    expose,
    update
  )
end

end

end
