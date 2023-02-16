module Visualization

using ..Core 
using ..Core: Constructor, InContext, name

using DataStructures

function Base.show(io::IO, m::MIME"text/plain", t::Theory)  
  println(io,"##########\n# Theory #\n##########\nType Constructors\n=================")
  for x in vcat(reverse(type_constructors(t))...)
    show(io,m,x) 
  end
  println(io,"\nTerm Constructors\n=================")
  for x in filter(x->arity(x)>0,vcat(reverse(term_constructors(t))...)) 
    show(io,m,x) 
  end
  println(io,"\nAxioms\n======")
  for x in vcat(axioms(t)...) 
    show(io,m,x) 
  end
  println(io,"\nConstants\n=========")
  for x in filter(x->arity(x)==0,vcat(term_constructors(t)...)) 
    show(io,m,x) 
  end
end 

Base.show(io::IO,m::MIME"text/plain",t::TypeConstructor) = show(io,m,sequent(t)) 
Base.show(io::IO,m::MIME"text/plain",t::TermConstructor) = show(io,m,sequent(t)) 
Base.show(io::IO,m::MIME"text/plain",t::Axiom) = show(io,m,sequent(t)) 

"""Intermediate representation of a judgment for pretty printing"""
struct Sequent 
  name::String
  ctx::Vector{Pair{Vector{String}, String}} 
  judgment::String
end 

function Base.show(io::IO,::MIME"text/plain",s::Sequent)
  numerator = join(["($(join(xs, ","))):$t" for (xs,t) in s.ctx], " | ")
  n = maximum(length.([numerator, s.judgment])) + 2
  off_n,off_d = [repeat(" ",(n-length(x))÷2) for x in [numerator, s.judgment]]
  title = repeat("-", n) * "  " * s.name
  println(io,join([off_n * numerator, title, off_d * s.judgment,""], "\n"))
end

show_type(t::TermConstructor) = show_inctx(t.ctx, t.typ)

function sequent(t::Constructor)
  arg_syms = [show_cons(t.ctx,i,j) for (i,j) in args(t)]
  typ = t isa TermConstructor ? ": $(show_type(t))" : ""
  arg = isempty(arg_syms) ? "" : "($(join(arg_syms, ",")))"
  Sequent("$(t.name) introduction", 
          extract_ctx(t.ctx), "$(t.name)$arg $typ")
end 

function sequent(t::Axiom)
  t1,t2 = [show_cons(t.ctx,i,j) for (i,j) in [t.lhs,t.rhs]]
  typ = show_type(t.ctx, t.type)
  Sequent(t.name, extract_ctx(t.ctx), "$t1 = $t2 : $typ")
end

"""Gets term constructor by default, term=false to get type constructor"""
function debruijn_to_cons(t::Theory, lvl::Int,i::Int; term=true)
  println("ACCESSING DEBRUIJN $lvl@$i")
  if lvl == 0
    return term ? t.term_constructors[i] : t.type_constructors[i]
  else
    return debruijn_to_cons(t, lvl-1, i)
  end
end

function show_cons(c::Constructor)
  a = isempty(c.args) ? "" : "($(join([show_cons(c.theory,c.args...)],",")))"
  return "$(name(c))$a"
end

function show_inctx(t::Theory, tic::InContext) 
  f = show_cons(t, headof(tic)...; term=tic isa TermInContext)
  a = isempty(args(tic)) ? "" : "($(join([show_inctx(t,a) for a in tic.args],",")))"
  return "$f$a"
end

show_cons(t::Theory, lvl::Int,i::Int; term=true) = 
  show_cons(debruijn_to_cons(t,lvl,i; term=term))

"""GET ALL ZERO ARITY TERM CONSTRUCTORS IN A THEORY"""
function extract_ctx(t::Theory)
  typdict = DefaultOrderedDict{String,Vector{String}}(()->String[])
  for con in filter(x->arity(x)==0,vcat(term_constructors(t)...)) 
    k,v = string.([show_type(con), name(con)])
    push!(typdict[k],v)
  end
  # [["foo","bar"]=>"Baz",["α,β"]=>"Λ(Θ,Ω)"]
  return [v=>k for (k,v) in collect(typdict)]
end 
arity(x) = length(args(x))


end # module 