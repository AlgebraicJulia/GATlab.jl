module Backend
export Lvl, ArgLvl, Typ, Trm, TypCon, TrmCon, Axiom, Context, Judgment, Theory, ThEmpty

using StructEquality

using ...Util
using ..Frontend

const Lvl = Int
const ArgLvl = Int

@struct_hash_equal struct Trm
  head::Lvl
  args::Vector{Trm}
end

@struct_hash_equal struct Typ
  head::Lvl
  args::Vector{Trm}
end

const Context = Vector{Tuple{Name, Typ}}

abstract type JudgmentHead end

@struct_hash_equal struct Judgment
  name::Name
  head::JudgmentHead
  ctx::Context
end

@struct_hash_equal struct TrmCon <: JudgmentHead
  args::Vector{ArgLvl}
  typ::Typ
end

@struct_hash_equal struct TypCon <: JudgmentHead
  args::Vector{ArgLvl}
end

@struct_hash_equal struct Axiom <: JudgmentHead
  typ::Typ
  equands::Vector{Trm}
end

@struct_hash_equal struct Theory
  orig::Frontend.Theory
  name::Name
  judgments::Vector{Judgment}
end

function levelize(typ::Frontend.Typ, n::Int)
  Typ(n - typ.head, levelize.(typ.args, Ref(n)))
end

function levelize(trm::Frontend.Trm, n::Int)
  Trm(n - trm.head, levelize.(trm.args, Ref(n)))
end

function levelize(typcon::Frontend.TypCon, n::Int, k::Int)
  TypCon(map(i -> k - i + 1, typcon.args))
end

function levelize(trmcon::Frontend.TrmCon, n::Int, k::Int)
  TrmCon(map(i -> k - i + 1, trmcon.args), levelize(trmcon.typ, n+k))
end

function levelize(axiom::Frontend.Axiom, n::Int, k::Int)
  Axiom(levelize(axiom.typ, n+k), levelize.(axiom.equands, Ref(n+k)))
end

function Theory(ft::Frontend.Theory)
  judgments = map(enumerate(ft.context)) do (n,j)
    ctx = map(enumerate(j.ctx)) do (i, j′)
      typeof(j′.head) == Frontend.TrmCon && length(j′.ctx) == 0 ||
        error("the context of a judgment should only consist of nullary term constructors")
      Tuple{Name, Typ}((j′.name, levelize(j′.head.typ, i + n - 1)))
    end
    Judgment(j.name, levelize(j.head, n, length(j.ctx)), ctx)
  end
  Theory(ft, ft.name, judgments)
end

const ThEmpty = Theory(Frontend.ThEmpty)

const Composite = Union{Typ, Trm, Nothing}

@struct_hash_equal struct TheoryMap
  dom::Theory
  codom::Theory
  composites::Vector{Composite}
end

function TheoryMap(ftm::Frontend.TheoryMap)
  TheoryMap(
    Theory(ftm.dom),
    Theory(ftm.codom),
    map(zip(ftm.dom.context, ftm.composites)) do (j, cmpst)
      if isnothing(cmpst)
        nothing
      else
        levelize(cmpst, length(ftm.codom.context) + length(j.ctx) - 1)
      end
    end
  )
end

end
