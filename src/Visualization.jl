module Visualization

using ..GATs 
using ..GATs: EmptyTheory, Constructor, Judgment, InContext, name, arity, 
              debruijn_to_cons, is_context, meet, 
              all_typecons, all_termcons, all_axioms

using DataStructures

function Base.show(io::IO, m::MIME"text/plain", t::Theory)  
  n = isempty(string(name(t))) ? "[theory]" : name(t)
  n_name = repeat('#',length(string(n)) + 4)

  println(io,"$n_name\n# $n #\n$n_name\nType Constructors\n=================")
  for (_,xs) in reverse(all_typecons(t))
    for x in xs 
      show(io,m,sequent(x)) 
    end
  end
  println(io,"\nTerm Constructors\n=================")
  for (_,xs) in reverse(all_termcons(t))
    for x in filter(x-> arity(x) > 0, xs)
      show(io,m,sequent(x)) 
    end
  end
  println(io,"\nAxioms\n======")
  for (_, xs) in reverse(all_axioms(t)) 
    for x in xs 
      show(io,m,sequent(x)) 
    end
  end
  println(io,"\nConstants\n=========")
  for (_,xs) in reverse(all_termcons(t))
    for x in filter(x-> arity(x) == 0, xs)
      show(io,m,sequent(x)) 
    end
  end
end 

"""Intermediate representation of a judgment for pretty printing"""
struct Sequent 
  name::String
  ctx::String
  judgment::String
end 

Base.show(io::IO,m::MIME"text/plain",j::Judgment) = show(io,m,sequent(j)) 

Base.show(io::IO,m::MIME"text/plain",c::Context) = show(io,m,ctx_string(c)) 



function Base.show(io::IO,::MIME"text/plain",s::Sequent)
  numerator = s.ctx
  n = maximum(length.([numerator, s.judgment])) + 2
  off_n,off_d = [repeat(" ",(n-length(x))÷2) for x in [numerator, s.judgment]]
  title = repeat("-", n) * "  " * s.name
  println(io,join([off_n * numerator, title, off_d * s.judgment,""], "\n"))
end

show_type(t::TermCon) = show_inctx(codom(t.ctx), t.typ)

function sequent(t::Constructor)
  C = ctx(t)
  arg_syms = [show_cons(codom(C),i,j) for (i,j) in args(t)]
  typ = t isa TermCon ? ": $(show_type(t))" : ": TYPE"
  arg = isempty(arg_syms) ? "" : "($(join(arg_syms, ",")))"
  Sequent("$(t.name) introduction", 
    ctx_string(C), "$(t.name)$arg $typ")
end 

function sequent(t::Axiom)
  C = ctx(t)
  T = codom(C)
  t1,t2 = [show_inctx(T,x) for x in [t.lhs,t.rhs]]
  typ = show_inctx(T, t.type)
  Sequent(string(t.name), 
    ctx_string(C), "$t1 = $t2 : $typ")
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


ctx_string(c::Context) = join(map(ctx_dict(c)) do (xs,t)
    if length(xs) == 0 return "" end 
    (length(xs)==1 ? only(xs) : "($(join(xs, ",")))") * ":$t" 
  end, " | ")



"""
Get the strings required to print the a context t1 that extends t2.
E.g. [["a","b","c"]=>"Ob", ["f","g"]=>["Hom(a,b)"], ...]
"""
function ctx_dict(t1::Theory,t2::Theory=nothing)
  ctx_terms = is_context(t1, t2)
  typdict = DefaultOrderedDict{String,OrderedSet{String}}(()->OrderedSet{String}())
  for con_idx in ctx_terms
    con = debruijn_to_cons(t1, con_idx...)
    k,v = string.([show_type(con), name(con)])
    push!(typdict[k],v)
  end 
  return [collect(v) => k for (k,v) in collect(typdict)]
end 
ctx_dict(c::Context) = ctx_dict(codom(c),dom(c))

end # module 