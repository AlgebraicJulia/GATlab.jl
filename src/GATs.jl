module GATs
export Name, Anon, Idx, TermCon, TypeCon, Trm, Typ, Axiom, Theory, Context, Judgment,
  extend, args, ThEmpty

using ..Lists
using StructEquality

# Indexing
##########

const Idx = Int

# Terms
#######

abstract type InContext end # Trm, Typ

abstract type Name end
struct Literal <: Name 
  name::String 
end

Name(n::String) = Literal(n)
Name(n::Name) = n
Name(n::Symbol) = Literal(string(n))

struct Anon <: Name
end

const INTMIN = (;init=typemin(Int))

"""
head - indexes term constructors in an (implicit) theory
args - arguments that the term constructor is applied to
"""
@struct_hash_equal struct Trm <: InContext
  head::Idx # debruijn index into the term context
  args::Vector{Trm}
  Trm(h,a=Trm[]) = new(Idx(h),a)
end

@struct_hash_equal struct Typ <: InContext
  head::Idx # debruijn index into the type context
  args::Vector{Trm}
  Typ(h,a=Trm[]) = new(Idx(h),a)
end

head(t::InContext) = t.head
args(t::InContext) = t.args

# Judgments
############

abstract type JudgmentHead end
abstract type Constructor <: JudgmentHead end 

"""
name - just documentation (and for rendering)
"""
struct Judgment
  name::Name
  ctx::AbstractVector{Judgment}
  head::JudgmentHead
  Judgment(n,c,h) = new(Name(n),c,h)
end

Base.:(==)(x::Judgment, y::Judgment) = x.head == y.head && x.ctx == y.ctx 
Base.hash(x::Judgment, h::UInt64) = hash(x.ctx, hash(x.head, h))

Base.nameof(x::Judgment) = x.name

const Context = AbstractVector{Judgment}

"""
A type constructor

args - indexes the ctx. I.e. "1" refers to the first term constructor in the 
       codom of the context. This subset ought be sufficient to type infer every  
       constant introduced in the context.
"""
@struct_hash_equal struct TypeCon <: Constructor
  args::Vector{Idx}
  TypeCon(a=Idx[]) = new(a)
end

"""
A term constructor

typ  - output type of applying the term constructor
args - indexes the ctx.
"""
@struct_hash_equal struct TermCon <: Constructor
  typ::Typ
  args::Vector{Idx}
  TermCon(t,a=Idx[]) = new(t,a)
end

args(x::Constructor) = x.args
arity(x::Constructor) = length(args(x))

"""
equands - the things being equated 
"""
@struct_hash_equal struct Axiom <: JudgmentHead
  type::Typ
  equands::Vector{Trm}
  Axiom(t,ts) = new(t,ts)
end

ctx(x::Judgment) = x.ctx
name(x::Judgment) = x.name

function maxind(c::Context)
  maximum(maxind(j) - i + 1 for (i,j) in enumerate(c); INTMIN...)
end

function maxind(j::Judgment)
  max(
    maxind(j.head) - length(j.ctx),
    maxind(j.ctx)
  )
end

function maxind(termcon::TermCon)
  max(
    maxind(termcon.typ),
    maximum(termcon.args; INTMIN...)
  )
end

maxind(typecon::TypeCon) = maximum(typecon.args; INTMIN...)

function maxind(axiom::Axiom)
  max(
    maxind(axiom.type),
    maximum(maxind.(axiom.equands); INTMIN...)
  )
end

maxind(t::InContext) = max(head(t), maximum(maxind.(args(t)); INTMIN...))

struct Theory 
  name::Name
  context::Context
  function Theory(n,context)
    maxind(context) <= 0 || error("Bad context: theory $n must be closed")
    return new(Name(n),context)
  end
end

Base.collect(t::Theory) = collect(t.context)
Base.length(t::Theory) = length(t.context)


function extend(t::Theory, n, js::AbstractVector{Judgment})
  Theory(
    n,
    vcat(t.context, js)
  )
end

const ThEmpty = Theory(Anon(), Bwd{Judgment}())

end # module
