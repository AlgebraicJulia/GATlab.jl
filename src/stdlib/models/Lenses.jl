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

function mcompose(a₁::SimpleArena{T}, a₂::SimpleArena{T}) where {T <: AbstractTheory}
  SimpleArena{T}(
    coproduct(a₁.pos, a₂.pos),
    coproduct(a₁.dir, a₂.dir)
  )
end

function permute(ctxs::Vector{Context}, permutation::Vector{Int})
  values = Trm[]
  for i in permutation
    c = ctxs[ctxs]
    offset = length(values)
    append!(values, Trm[Trm(Lvl(i + offset; context=true)) for i in 1:length(c)])
  end
end

"""
l₁ = (f, f#)
l₂ = (g, g#)

l = l₁ ⋅ l₂

l = (h, h#)

    f#
B1 <-- D1
    f
A1 --> C1

    g#
B2 <-- D2
    g
A2 --> C2

             f + g
h = C1 + C2 -------> A1 + A2

              f# + g#                          1_A1 + σ_{D_1,A_2} + 1_D2
h# = B1 + B2 ---------> (A1 + D1) + (A2 + D2) ----------------------------> (A1 + A2) + (D1 + D2)
"""
function mcompose(l₁::SimpleKleisliLens{T}, l₂::SimpleKleisliLens{T}) where {T <: AbstractTheory}
  SimpleKleisliLens{T}(
    coproduct(l₁.dom, l₂.dom),
    coproduct(l₁.codom, l₂.codom),
    coproduct_values(l₁.expose, l₂.expose, length(l₁.dom.pos)),
    substitute_all(
      coproduct_values(l₁.update, l₂.update, length(l₁.dom.dir)),
      permute([l₁.dom.pos, l₁.codom.dir, l₂.dom.pos, l₂.codom.dir], [1,3,2,4])
    )
  )
end

#end

end
