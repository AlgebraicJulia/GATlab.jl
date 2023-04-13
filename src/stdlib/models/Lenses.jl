module Lenses

using ....Syntax
using ....Models
using ...StdTheories

struct SimpleArena
  pos::Context
  dir::Context
end

"""
expose is a Kleisli map from codom.pos to dom.pos
update is a Kleisli map from dom.dir to codom.dir + dom.pos
"""
struct SimpleKleisliLens
  dom::SimpleArena
  codom::SimpleArena
  expose::Vector{Trm}
  update::Vector{Trm}
end

struct SimpleLensC{T<:AbstractTheory} <: Model{ThStrictMonCat}
end

end
