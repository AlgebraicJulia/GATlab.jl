module Lenses

export SimpleArena, SimpleKleisliLens, compose

using ....Syntax
using ....Logic
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

# Either{A,A} -> A
# Left(a) |-> a
# Right(a) |-> a

#module SimpleKleisliLensImpl

function codiag(c::Context)
  vcat(id_values(c), id_values(c))
end

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

       g      f
h = E ---> C ---> A

        f#        1_A+g#             1_A + f + 1_F              ∇_A + 1_F
h# = B --> A + D -------> A + C + F ---------------> A + A + F -----------> A + F
"""
function compose(l₁::SimpleKleisliLens{T}, l₂::SimpleKleisliLens{T}) where {T <: AbstractTheory}
  expose = substitute_all(l₂.expose, l₁.expose)
  A_n = length(l₁.dom.pos)
  update = substitute_all(
    l₁.update,
    coproduct_values(id_values(l₁.dom.pos), l₂.update, A_n),
    coproduct_values(id_values(l₁.dom.pos), coproduct_values(l₁.expose, id_values(l₂.codom.dir), A_n), A_n),
    coproduct_values(codiag(l₁.dom.pos), id_values(l₂.codom.dir), A_n)
  )
  SimpleKleisliLens{T}(
    l₁.dom,
    l₂.codom,
    expose,
    update
  )
end

#end

end
