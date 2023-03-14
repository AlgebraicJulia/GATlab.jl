module DataStructures

struct Intrd{T}
  id::Int
end

struct Registry{T}
  next::Ref{Int}
  store::Dict{T, Intrd{T}}
  lookup::Dict{Intrd{T}, T}
end

function inter!(registry::Registry{T}, x::T) where {T}
  if x ∈ keys(store)
    return store[x]
  end
  i = Intrd{T}(registry.next[]++)
  store[x] = i
  lookup[i] = x
  i
end

struct MultiSet{T}
  arity::Dict{Intrd{T}, Int}
end

struct Idx{T}
  val::Intrd{T}
  idx::Int
end

abstract type JudgmentHead

struct Judgment
  head::JudgmentHead
  ctx::MultiSet{Judgment}
end

const JIdx = Idx{Judgment}

const Context = MultiSet{Judgment}

struct Trm
  head::JIdx
  args::Vector{Trm}
end

struct Typ
  head::JIdx
  args::Vector{Trm}
end

struct TermCon <: JudgmentHead
  args::Vector{JIdx}
  typ::Typ
end

struct TypeCon <: JudgmentHead
  args::Vector{JIdx}
end

struct Axiom <: JudgmentHead
  lhs::Trm
  rhs::Trm
  type::Typ
end

struct JudgmentNaming
  namelookup::Dict{JIdx, Tuple{Name, JudgmentNaming}}
end

struct Theory
  name::Name
  context::Context
  naming::JudgmentNaming
end

end
