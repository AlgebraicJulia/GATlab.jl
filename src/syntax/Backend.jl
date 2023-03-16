module Backend
export Lvl, ArgLvl, Typ, Trm, TypCon, TrmCon, Axiom, Context, Judgment, Theory, ThEmpty

using StructEquality

using ...Util
using ..Frontend

const Lvl = Int
const ArgLvl = Int

abstract type TrmTyp end 

@struct_hash_equal struct Trm <:TrmTyp
  head::Lvl
  args::Vector{Trm}
end

@struct_hash_equal struct Typ <: TrmTyp
  head::Lvl
  args::Vector{Trm}
end

const Context = Vector{Tuple{Name, Typ}}

abstract type JudgmentHead end
abstract type Constructor <: JudgmentHead end 
args(c::Constructor) = c.args

struct Judgment
  name::Name
  head::JudgmentHead
  ctx::Context
end

Base.:(==)(x::Judgment,y::Judgment) = x.head == y.head && x.ctx && y.ctx
Base.hash(x::Judgment, h) = hash(x.head, hash(x.ctx, h))
name(j::Judgment) = j.name

# Args index the CONTEXT of the judgment
@struct_hash_equal struct TrmCon <: Constructor
  args::Vector{ArgLvl}
  typ::Typ
end

# Args index the CONTEXT of the judgment
@struct_hash_equal struct TypCon <: Constructor
  args::Vector{ArgLvl}
end


@struct_hash_equal struct Axiom <: JudgmentHead
  typ::Typ
  equands::Vector{Trm}
  function Axiom(t,e)
    length(unique(e)) > 1 || error("Axiom must be nontrivial")
    return new(t,e)
  end
end

struct Theory
  orig::Frontend.Theory
  name::Name
  judgments::Vector{Judgment}
end

Base.:(==)(x::Theory,y::Theory) = x.judgments == y.judgments
Base.hash(x::Theory, h) = hash(x.judgments, h)
Base.getindex(t::Theory,i::Int) = t.judgments[i]
Base.length(t::Theory) = t.judgments |> length


"""Converts de bruijn index to de bruijn level"""
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
