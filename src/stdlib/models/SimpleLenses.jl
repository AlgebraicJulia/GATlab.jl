module SimpleLenses
export SimpleKleisliLens, SimpleArena

using ...StdTheories
using ....Models
using ....Syntax
using ..ContextMaps

module Impl

using .....Syntax
using .....Models
using ....StdTheories
using ...ContextMaps

const CM = ContextMaps.Impl

struct Arena{T<:AbstractTheory}
  pos::Context
  dir::Context
end

const Ob = Arena

"""
expose is a Kleisli map from codom.pos to dom.pos
update is a Kleisli map from dom.dir to dom.pos + codom.dir
"""
struct Lens{T<:AbstractTheory}
  expose::Vector{Trm}
  update::Vector{Trm}
end

const Hom = Lens

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


# TODO
Should write down:

  fs ⋅ (id(A) + gs) ⋅ (id(A) + f + id(F)) ⋅ (∇(A) + id(F))

as a Trm in the theory of cocartesian monoidal categories, and then interpret it.
"""
function compose(AB::Arena{T}, CD::Arena{T}, EF::Arena{T}, f::Lens{T}, g::Lens{T}) where {T <: AbstractTheory}
  expose = CM.compose(g.expose, f.expose)
  A = AB.pos
  F = EF.dir
  A_n = length(A)
  update = CM.compose(
    f.update,
    CM.mcompose(CM.id(A), g.update, A_n),
    CM.mcompose(CM.id(A), CM.mcompose(f.expose, CM.id(F), A_n), A_n),
    CM.mcompose(CM.codiag(A), CM.id(F), A_n)
  )
  Lens{T}(expose, update)
end

function mcompose(a₁::Arena{T}, a₂::Arena{T}) where {T <: AbstractTheory}
  Arena{T}(
    CM.mcompose(a₁.pos, a₂.pos),
    CM.mcompose(a₁.dir, a₂.dir)
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

              f# + g#                          1_A1 + σ_{D1,A2} + 1_D2
h# = B1 + B2 ---------> (A1 + D1) + (A2 + D2) ----------------------------> (A1 + A2) + (D1 + D2)
"""
function mcompose(AB₁::Arena{T}, AB₂::Arena{T}, CD₁::Arena{T}, CD₂::Arena{T},
                  f::Lens{T}, g::Lens{T}) where {T <: AbstractTheory}
  A₁, A₁ = AB₁.pos, AB₂.pos
  B₁ = AB₁.dir
  D₁, D₂ = CD₁.dir, CD₂.dir
  Lens{T}(
    CM.mcompose(f.expose, g.expose, length(A₁)),
    CM.compose(
      CM.mcompose(f.update, g.update, length(B₁)),
      permute([A₁, D₁, A₂, D₂], [1,3,2,4])
    )
  )
end

end

struct SimpleKleisliLens{T<:AbstractTheory} <: TypedHom{Impl.Arena{T}, Impl.Lens{T}}
  dom::Impl.Arena{T}
  codom::Impl.Arena{T}
  morphism::Impl.Lens{T}
  function SimpleKleisliLens{T}(
    dom::Impl.Ob{T}, codom::Impl.Ob{T},
    expose::Vector{Trm}, update::Vector{Trm}
  ) where {T<: AbstractTheory}
    new(dom, codom, Impl.Lens{T}(expose, update))
  end
  function SimpleKleisliLens{T}(
    dom::Impl.Ob{T}, codom::Impl.Ob{T},
    morphism::Impl.Lens{T}
  ) where {T<: AbstractTheory}
    new(dom, codom, morphism)
  end
end

const SimpleArena = Impl.Arena

Categories.compose(f::SimpleKleisliLens{T}, g::SimpleKleisliLens{T}) where {T<:AbstractTheory} =
  SimpleKleisliLens{T}(
    f.dom,
    g.codom,
    Impl.compose(
      f.dom,
      f.codom,
      g.codom,
      f.morphism,
      g.morphism
    )
  )

function Base.show(io::IO, l::SimpleKleisliLens{T}) where {T<:AbstractTheory}
  theory = gettheory(T)
  println(io, "dom: ", l.dom)
  println(io, "codom: ", l.codom)

  println(io, "expose: ")
  show_context_map(io, theory, l.codom.pos, l.dom.pos, l.morphism.expose)
  println(io)
  println(io, "update: ")
  show_context_map(io, theory, l.dom.dir, Impl.CM.mcompose(l.dom.pos, l.codom.dir), l.morphism.update)
  println(io)
end

end
