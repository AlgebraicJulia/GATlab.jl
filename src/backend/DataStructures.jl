module DataStructures
using StructEquality

using ...Util

const Lvl = Int
const ArgIdx = Int

@struct_hash_equal struct Trm
  head::Lvl
  args::Fwd{Lvl}
end

@struct_hash_equal struct Typ
  head::Lvl
  args::Fwd{Lvl}
end

abstract type JudgmentHead

@struct_hash_equal struct Judgment
  name::Name
  head::JudgmentHead
  ctx::Fwd{Tuple{Name, Typ}}
end

@struct_hash_equal struct TrmCon <: JudgmentHead
  args::Fwd{ArgLvl}
  typ::Typ
end

@struct_hash_equal struct TypCon <: JudgmentHead
  args::Fwd{ArgLvl}
end

@struct_hash_equal struct Axiom <: JudgmentHead
  lhs::Trm
  rhs::Trm
  type::Typ
end

const Context = Fwd{Context}

@struct_hash_equal struct Theory
  name::Name
  context::Context
end

end
