module Backend
export Lvl, ArgLvl, Typ, Trm, TypCon, TrmCon, Axiom, Context, Judgment, Theory, ThEmpty, index, is_context

using StructEquality

using ...Util
using ..Frontend

struct Lvl
  val::UInt64
  function Lvl(i::Integer; context=false)
    i > 0 || error("Creating non-positive level $i context $context")
    new(UInt64(i) | (UInt64(context) << 63))
  end
end
"""N is length of theory"""
function Lvl(i::Integer, n::Integer) 
  i > n ? Lvl(i-n; context=true) : Lvl(i)
end


const CONTEXT_BIT = UInt64(1) << 63

is_context(i::Lvl) = (i.val & CONTEXT_BIT) != 0

index(i::Lvl) = i.val & (CONTEXT_BIT - 1)

abstract type TrmTyp end 

@struct_hash_equal struct Trm <:TrmTyp
  head::Lvl
  args::Vector{Trm}
  function Trm(l::Lvl,a=Trm[])
    (is_context(l) && !isempty(a)) || error("Elements of context are *nullary* type constructors")
    return new(l,a)
  end
  function Trm(l::Int,a=Trm[])
    return new(Lvl(l), a)
  end
end

"""
The head of a type can never come from a context, only a theory, because it 
should point at a type constructor judgment.
"""
@struct_hash_equal struct Typ <: TrmTyp
  head::Lvl
  args::Vector{Trm}
  function Typ(l,a=Lvl[]) 
    !is_context(l) || error("Bad head for type: $(index(l))")
    return new(l,a)
  end 
end


struct Context 
  ctx::Vector{Tuple{Name, Typ}}
  Context(c=Tuple{Name, Typ}[]) = new(c)
end 

Base.getindex(c::Context,i::Lvl) = is_context(i) ? c.ctx[index(i)] : error("$i")
Base.collect(c::Context) = collect(c.ctx)
Base.length(c::Context) = length(c.ctx)
Base.iterate(c::Context,i) = iterate(c.ctx,i)
Base.iterate(c::Context,) = iterate(c.ctx)

abstract type JudgmentHead end
abstract type Constructor <: JudgmentHead end 
args(c::Constructor) = c.args

struct Judgment
  name::Name
  head::JudgmentHead
  ctx::Context
  Judgment(n,h,c=Context()) = new(n,h,c)
end

Base.:(==)(x::Judgment,y::Judgment) = x.head == y.head && x.ctx == y.ctx
Base.hash(x::Judgment, h) = hash(x.head, hash(x.ctx, h))
name(j::Judgment) = j.name

# Args index the CONTEXT of the judgment
@struct_hash_equal struct TrmCon <: Constructor
  args::Vector{Lvl}
  typ::Typ
  function TrmCon(a,t)
    all(is_context, a) || error("Args for term constructor must refer to the context")
    return new(a,t)
  end
end

# Args index the CONTEXT of the judgment
@struct_hash_equal struct TypCon <: Constructor
  args::Vector{Lvl}
  function TypCon(a::AbstractVector{Lvl})
    all(is_context, a) || error("Args for type constructor must refer to the context")
    return new(a)
  end
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
Base.getindex(t::Theory,i::Lvl) = 
  is_context(i) ? error("Bad index $i") : t.judgments[index(i)]
Base.length(t::Theory) = t.judgments |> length


"""Converts de bruijn index to de bruijn level
n = theory length
k = context length
"""
function levelize(typ::Frontend.Typ, n::Int, k::Int)
  Typ(Lvl(n + k + 1 - typ.head, n), levelize.(typ.args, Ref(n), Ref(k)))
end

function levelize(trm::Frontend.Trm, n::Int, k::Int)
  Trm(Lvl(n + k + 1 - trm.head, n), levelize.(trm.args, Ref(n), Ref(k)))
end

function levelize(typcon::Frontend.TypCon, n::Int, k::Int)
  TypCon(map(i -> Lvl(n+k+1-i, n), typcon.args))
end

function levelize(trmcon::Frontend.TrmCon, n::Int, k::Int)
  TrmCon(map(i -> Lvl(n+k+1-i, n), trmcon.args), levelize(trmcon.typ, n, k))
end
function levelize(axiom::Frontend.Axiom, n::Int, k::Int)
  Axiom(levelize(axiom.typ, n, k), levelize.(axiom.equands,Ref(n),Ref(k)))
end

function levelize(ctx::AbstractVector{Frontend.Judgment}, n::Int)
  Context(
    map(enumerate(ctx)) do (i, j′)
      typeof(j′.head) == Frontend.TrmCon && length(j′.ctx) == 0 ||
        error("the context of a judgment should only consist of nullary term constructors")
      Tuple{Name, Typ}((j′.name, levelize(j′.head.typ, n, i-1)))
    end
  )
end

function levelize(j::Frontend.Judgment, n::Int)
  ctx = levelize(j.ctx, n)
  Judgment(j.name, levelize(j.head, n, length(j.ctx)), ctx)
end

function Theory(ft::Frontend.Theory)
  judgments = map(enumerate(ft.context)) do (n,j)
    levelize(j, n-1)
  end
  Theory(ft, ft.name, judgments)
end

const ThEmpty = Theory(Frontend.ThEmpty)

const Composite = Union{Typ, Trm, Nothing}

@struct_hash_equal struct TheoryMap
  dom::Theory
  codom::Theory
  composites::Vector{Composite}
  function TheoryMap(d,c,cs)
    lc, ld = length.([cs,d])
    lc == ld || error("Bad composite length: $lc != $ld")
    return new(d,c,cs)
  end
end

function TheoryMap(ftm::Frontend.TheoryMap)
  TheoryMap(
    Theory(ftm.dom),
    Theory(ftm.codom),
    map(zip(ftm.dom.context, ftm.composites)) do (j, cmpst)
      if isnothing(cmpst)
        nothing
      else
        levelize(cmpst, length(ftm.codom.context), length(j.ctx))
      end
    end
  )
end

Base.getindex(t::TheoryMap, i::Integer) = t.composites[i]
Base.collect(t::TheoryMap) = collect(t.composites)
Base.length(t::TheoryMap) = length(t.composites)
(t::TheoryMap)(i::Integer) = t[i]

"""Map a context in the domain theory into a context of the codomain theory"""
(f::TheoryMap)(c::Context) =  Context([(a,f(b)) for (a,b) in c.ctx])

"""
Suppose dom(f) is [X,Y,Z,P,Q] and codom(f) is [XX,ϕ,ψ]
suppose we have a term: P(a,Q(b,c)) ⊢ a::X,b::Y,c::Z i.e. 4({1},5({2},{3}))

f maps all sorts to XX
f maps {P(x,y) ⊢ x::X,y::Y} to ϕ(ψ(y),x) i.e. 2(3({2}),{1})
and {Q(u,w) ⊢ u::Y,w::Z}    to ψ(w)      i.e. 3({2})

We should our term translate first to ϕ(ψ(y),x)  i.e.  2(3({2}),{1})

and then substitute x (i.e. {1}) for the mapped first argument 
y (i.e. 5) for f(q(b,c)) i.e. ϕ(ψ(ψ(c)),x) 2(3(3({3})),{1})

So f(4({1},5({2},{3}))) = 2(3(3({3})),{1})
"""
function (f::TheoryMap)(t::TrmTyp)  # e.g. P(a,q(b,c)) i.e. 4({1},5({2},{3}))
  if is_context(t.head) return t end  
  new_trm = f(index(t.head)) # e.g. ϕ(ψ(y),x) i.e. 2(3({2}),{1})
  n_args = f.(t.args) # [{1},3({3})] 
  old_j = f.dom[t.head]
  subs = Vector{Union{Nothing,Trm}}(fill(nothing, length(old_j.ctx)))
  for (i,a) in enumerate(old_j.head.args)
    subs[index(a)] = n_args[i]
  end
  return substitute(new_trm, subs)
end 

substitute(t::T, ts::Vector{Union{Nothing,Trm}}) where {T<:TrmTyp} = 
  is_context(t.head) ? ts[index(t.head)] : T(t.head, substitute.(t.args, Ref(ts)))
end