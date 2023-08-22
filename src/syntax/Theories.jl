module Theories
export TypTag, TrmTag, AnonTypTag, AnonTrmTag,
  Axiom, Judgment, Theory,
  AbstractTheory, gettheory, empty_theory, ThEmpty, index, is_context,
  getlevel, FullContext, lookup, arity, judgments,
  rename, getname, SortSignature, Constructor, getsort, Constructor,
  exported_names, typcons, trmcons, derive_context_from_args,
  ArgExpr, IndirectArg, DirectArg

using StructEquality
using MLStyle

using ...Util
using ..Syntax
import ..Syntax: headof, argsof, typof

abstract type JudgmentBody end

struct Judgment
  name::Name
  body::JudgmentBody
  context::Context
  Judgment(n, h, c=Context()) = new(n, h, c)
end

Base.hash(x::Judgment, h) = hash(x.head, hash(x.ctx, h))
getname(j::Judgment) = j.name
rename(j::Judgment, n::Name) = Judgment(n, j.head, j.ctx)
bodyof(j::Judgment) = j.body
contextof(j::Judgment) = j.context
Base.:(==)(x::Judgment, y::Judgment) = headof(x) == headof(y) && contextof(x) == contextof(y)

abstract type Constructor <: JudgmentBody end

argsof(c::Constructor) = c.args

# Args index the context of the judgment
@struct_hash_equal struct TrmCon <: Constructor
  args::Vector{Lvl}
  typ::Typ
  function TrmCon(a,t)
    all(is_context, a) || error("Args for term constructor must refer to the context")
    return new(a,t)
  end
end

argsof(con::TrmCon) = con.args
typof(con::TrmCon) = con.typ


# Args index the CONTEXT of the judgment
@struct_hash_equal struct TypCon <: Constructor
  args::Vector{Lvl}
  function TypCon(a::AbstractVector{Lvl})
    all(is_context, a) || error("Args for type constructor must refer to the context")
    return new(a)
  end
end

arity(f::Constructor) = length(f.args)

@struct_hash_equal struct Axiom <: JudgmentBody
  typ::Typ
  equands::Vector{Trm}
  function Axiom(t,e)
    length(unique(e)) > 1 || error("Axiom must be nontrivial")
    return new(t, e)
  end
end

@struct_hash_equal struct SortSignature
  name::Name
  sorts::Vector{Lvl}
  function SortSignature(j::Judgment)
    j.head isa Constructor || error("Only can take the SortSignature of a constructor")
    new(j.name, Lvl[j.ctx[i][2].head for i in j.head.args])
  end
  function SortSignature(n::Name, sorts::Vector{Lvl})
    new(n, sorts)
  end
end

struct Theory
  name::Name
  judgments::Vector{Judgment}
  aliases::Dict{SortSignature, Lvl}
  function Theory(name::Name, judgments::Vector{Judgment}, aliases=Dict{SortSignature, Lvl}())
    aliases = merge(
      aliases,
      Dict(SortSignature(j) => Lvl(i) for (i, j) in enumerate(judgments) if j.head isa Constructor)
    )
    new(name, judgments, aliases)
  end
end

Base.:(==)(x::Theory,y::Theory) = x.judgments == y.judgments
Base.hash(x::Theory, h) = hash(x.judgments, h)
Base.getindex(t::Theory,i::Lvl) = 
  is_theory(i) ? t.judgments[index(i)] : error("Bad index $i")
Base.length(t::Theory) = t.judgments |> length
judgments(t::Theory) = t.judgments

function exported_names(t::Theory)
  [
    [Symbol(j.name) for j in t.judgments if j.head isa Constructor];
    [Symbol(arg) for j in t.judgments if j.head isa TypCon for (arg, _) in j.ctx.ctx]
  ]
end

function typcons(t::Theory)
  filter(j -> j.head isa TypCon, t.judgments)
end

function trmcons(t::Theory)
  filter(j -> j.head isa TrmCon, t.judgments)
end

Context(T::Theory, c::AbstractVector{<:Name}) = 
  Context([(v,Typ(lookup(T, Default()))) for v in c])

"""
The full context for a `Trm` or `Typ` consists of both a theory and a context
"""
struct FullContext
  theory::Theory
  context::Context
end

theoryof(fc::FullContext) = fc.theory
contextof(fc::FullContext) = fc.context

function getsort(fc::FullContext, t::Trm)
  if is_theory(t.head)
    fc.theory.judgments[index(t.head)].head.typ.head
  else
    fc.context[t.head][2].head
  end
end

"""
Get the `Lvl` corresponding to a Name. This is the most recent judgment with
that name.
"""
function lookup(fc::FullContext, n::Name)
  i = findlast(nt -> nt[1] == n, fc.context.ctx)
  if !isnothing(i)
    return Lvl(i; context=true)
  end
  i = findlast(j -> j.name == n, fc.theory.judgments)
  if !isnothing(i)
    Lvl(i; context=false)
  else
    throw(KeyError(n))
  end
end

lookup(t::Theory, n::Name) = lookup(FullContext(t, Context()), n)
lookup(t::Theory, s::Symbol) = lookup(FullContext(t, Context()), Name(s))
lookup(fc::FullContext, s::Symbol) = lookup(fc, Name(s))

function lookup(fc::FullContext, sig::SortSignature)
  i = findlast(nt -> nt[1] == sig.name, fc.context.ctx)
  if !isnothing(i)
    return Lvl(i; context=true)
  end
  fc.theory.aliases[sig]
end

@data ArgExpr begin
  DirectArg(id::Int)
  IndirectArg(ty::Lvl, argidx::Int, expr::ArgExpr)
end

# Fill out an array the same length as the context, where each element is a vector of expressions
# for how to derive that variable from the arguments.
# Assumes `j` is a term constructor
function derive_context_from_args(t::Theory, j::Judgment)::Vector{Vector{ArgExpr}}
  arg_exprs = [ArgExpr[] for _ in j.ctx.ctx]
  to_expand = Tuple{ArgExpr, Lvl}[(DirectArg(idx), i) for (idx, i) in enumerate(j.head.args)]
  while !(isempty(to_expand))
    (argexpr, i) = pop!(to_expand)
    push!(arg_exprs[index(i)], argexpr)
    _, ty = j.ctx[i]
    for (argidx, arg) in enumerate(ty.args)
      if is_context(arg.head)
        push!(to_expand, (IndirectArg(ty.head, argidx, argexpr), arg.head))
      else
        # TODO: handle the case with a type constructor applied to term constructors
      end
    end
  end
  arg_exprs
end


end
