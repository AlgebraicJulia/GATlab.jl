module Visualization

using ..GATs 
using ..GATs: Constructor, InContext, name, arity, debruijn_to_cons

using DataStructures

function Base.show(io::IO, m::MIME"text/plain", t::Theory)  
  println(io,"##########\n# Theory #\n##########\nType Constructors\n=================")
  for (xt,xs) in reverse(typecons(t))
    for x in xs 
      show(io,m,sequent(xt,x)) 
    end
  end
  println(io,"\nTerm Constructors\n=================")
  for (xt,xs) in reverse(termcons(t))
    for x in filter(x-> arity(x) > 0, xs)
      show(io,m,sequent(xt,x)) 
    end
  end
  println(io,"\nAxioms\n======")
  for x in vcat(axioms(t)...) 
    show(io,m,sequent(x)) 
  end
  println(io,"\nConstants\n=========")
  for (xt,xs) in reverse(termcons(t))
    for x in filter(x-> arity(x) == 0, xs)
      show(io,m,sequent(xt,x)) 
    end
  end
end 

"""Intermediate representation of a judgment for pretty printing"""
struct Sequent 
  name::String
  ctx::Vector{Pair{Vector{String}, String}} 
  judgment::String
end 

function Base.show(io::IO,::MIME"text/plain",s::Sequent)
  numerator = join(map(s.ctx) do (xs,t)
    if length(xs) == 0 return "" end 
    (length(xs)==1 ? only(xs) : "($(join(xs, ",")))") * ":$t" 
  end, " | ")
  n = maximum(length.([numerator, s.judgment])) + 2
  off_n,off_d = [repeat(" ",(n-length(x))÷2) for x in [numerator, s.judgment]]
  title = repeat("-", n) * "  " * s.name
  println(io,join([off_n * numerator, title, off_d * s.judgment,""], "\n"))
end

show_type(t::TermCon) = show_inctx(t.ctx, t.typ)

function sequent(basetheory::Theory, t::Constructor)
  arg_syms = [show_cons(t.ctx,i,j) for (i,j) in args(t)]
  typ = t isa TermCon ? ": $(show_type(t))" : ": TYPE"
  arg = isempty(arg_syms) ? "" : "($(join(arg_syms, ",")))"
  Sequent("$(t.name) introduction", 
    ctx_diff(t.ctx, basetheory), "$(t.name)$arg $typ")
end 

function sequent(t::Axiom)
  t1,t2 = [show_inctx(t.ctx,x) for x in [t.lhs,t.rhs]]
  typ = show_inctx(t.ctx, t.type)
  Sequent(string(t.name), ctx_diff(t.ctx), "$t1 = $t2 : $typ")
end

function show_cons(c::Constructor)
  a = isempty(c.args) ? "" : "($(join([show_cons(c.ctx,x...) for x in c.args],",")))"
  return "$(name(c))$a"
end

function show_inctx(t::TheoryExt, tic::InContext)
  f = name(debruijn_to_cons(t, headof(tic)...; term=tic isa TermInContext))
  a = isempty(args(tic)) ? "" : "($(join([show_inctx(t,a) for a in tic.args],",")))"
  return "$f$a"
end

show_cons(t::Theory, lvl::Int,i::Int; term=true) = 
  show_cons(debruijn_to_cons(t,lvl,i; term=term))

"""GET ALL ZERO ARITY TERM CONSTRUCTORS IN A THEORY"""
function extract_consts(t::Theory)
  typdict = DefaultOrderedDict{String,OrderedSet{String}}(
    ()->OrderedSet{String}())

  for (_, xs) in reverse(termcons(t))
    for con in xs 
      if arity(con) == 0
        k,v = string.([show_type(con), name(con)])
        push!(typdict[k],v)
      end
    end 
  end 
  return typdict
end 

"""The difference between two contexts"""
ctx_diff(t1::Theory,t2::Theory) = ctx_diff(extract_consts.([t1,t2])...)
ctx_diff(t1::Theory) = ctx_diff(extract_consts(t1), DefaultOrderedDict(()->nothing))
ctx_diff(t1::DefaultOrderedDict,t2::DefaultOrderedDict) =
  [collect(setdiff(t1[k],get(t2,k,[]))) => k for k in keys(t1)]
 

end # module 