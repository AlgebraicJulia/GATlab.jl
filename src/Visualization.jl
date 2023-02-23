module Visualization
export show_term

using ..GATs 
using ..GATs: EmptyTheory, Constructor, Judgment, InContext, name, arity, 
              debruijn_to_cons, is_context, meet, 
              all_typecons, all_termcons, all_axioms, TheoryHom

using DataStructures

# Contexts 
##########
Base.show(io::IO,m::MIME"text/plain",c::Context) = show(io,m,ctx_string(c)) 

ctx_string(c::Context) = join(map(ctx_dict(c)) do (xs,t)
  if length(xs) == 0 return "" end 
  (length(xs)==1 ? only(xs) : "($(join(xs, ",")))") * ":$t" 
end, " | ")


"""
Get the strings required to print the a context t1 that extends t2.
E.g. [["a","b","c"]=>"Ob", ["f","g"]=>["Hom(a,b)"], ...]
"""
function ctx_dict(ext_theory::Theory,base_theory::Theory=nothing)
  ctx_terms = is_context(ext_theory, base_theory)
  # println("CTX TERMS $(name(ext_theory)) ↩ $(name(base_theory)) : $ctx_terms")
  typdict = DefaultOrderedDict{String,OrderedSet{String}}(()->OrderedSet{String}())
  for con_idx in ctx_terms
    con = debruijn_to_cons(ext_theory, con_idx)
    k,v = string.([show_type(con), name(con)])
    push!(typdict[k],v)
  end 
  return [collect(v) => k for (k,v) in collect(typdict)]
end 
ctx_dict(c::Context) = ctx_dict(codom(c),dom(c))

# Terms 
#######

"""Intermediate representation of a judgment for pretty printing"""
struct Sequent 
  name::String
  ctx::String
  judgment::String
end 


"""
Here we interpret a 
"""
function show_inctx(t::TheoryExt, tic::InContext)
  # println("showing tic $tic in theory $(name(t)) of length $(length(t))")
  f = name(debruijn_to_cons(t, headof(tic); term=tic isa TermInContext))
  a = isempty(args(tic)) ? "" : "($(join([show_inctx(t,a) for a in tic.args],",")))"
  return "$f$a"
end

function show_term(c::Context, tic::TermInContext) 
  Sequent("",ctx_string(c),show_inctx(codom(c),tic))
end


# Judgments 
###########
Base.show(io::IO,m::MIME"text/plain",j::Judgment) = show(io,m,sequent(j)) 


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
  arg_syms = [show_cons(codom(C),i) for i in args(t)]
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
  a = isempty(c.args) ? "" : "($(join([show_cons(c.ctx,x) for x in c.args],",")))"
  return "$(name(c))$a"
end
show_cons(t::Theory, i::DeBruijn; term=true) = 
  show_cons(debruijn_to_cons(t,i; term=term))


# Theories
##########

function Base.show(io::IO, m::MIME"text/plain", t::Theory)  
  n = isempty(string(name(t))) ? "[theory]" : name(t)
  n_name = repeat('#',length(string(n)) + 4)

  println(io,"$n_name\n# $n #\n$n_name\nType Constructors\n=================")
  for xs in reverse(all_typecons(t))
    for x in xs 
      show(io,m,sequent(x)) 
    end
  end
  println(io,"\nTerm Constructors\n=================")
  for xs in reverse(all_termcons(t))
    for x in filter(x-> arity(x) > 0, xs)
      show(io,m,sequent(x)) 
    end
  end
  println(io,"\nAxioms\n======")
  for xs in reverse(all_axioms(t)) 
    for x in xs 
      show(io,m,sequent(x)) 
    end
  end
  println(io,"\nConstants\n=========")
  for xs in reverse(all_termcons(t))
    for x in filter(x-> arity(x) == 0, xs)
      show(io,m,sequent(x)) 
    end
  end
end 


# Theory morphisms 
##################

function Base.show(io::IO,::MIME"text/plain",thom::TheoryHom)
  X,Y = dom(thom), codom(thom)
  nX,nY = name.([X, Y])
  tymap = join(reverse(vcat(map(enumerate(all_typecons(X))) do (d,tcs)  
    depth = d - 1
    map(enumerate(tcs)) do (i,tc)
      println("DEPTH $depth i $i")
      y = typemap(thom, DeBruijn(depth,i)) 
      return "$(name(tc)): $(name(debruijn_to_cons(Y,y; term=false)))"
    end
  end...)),", ")
  trmap = join(reverse(vcat(map(enumerate(all_termcons(X))) do (d,tcs) 
    depth = d - 1
    map(enumerate(tcs)) do (i,tc)
      trm = termmap(thom, DeBruijn(depth,i))
      as = args(trm)
      if all(a->a.depth==0, headof.(as)) && 1:length(as) == [z.idx for z in headof.(as)]
          tstr = name(debruijn_to_cons(Y, headof(trm))) # special case: easy!
      else 
        tctx = Context(Y, map(enumerate(tc.args)) do (i,a)
          arg_tcon = debruijn_to_cons(codom(tc.ctx), a)
          new_type = thom(Context(X),Context(Y),arg_tcon.typ+depth+1)
          TermCon(Y, Symbol("[$i]"),new_type, [f(X,Y,a+depth+1) for a in args(arg_tcon)])
        end)
        trm′ = map(x->x.depth==0 ? x : x+1, trm) # keep zeros, increment all else
        tstr = show_term(tctx, trm′).judgment
      end 
      return "$(name(tc)): $tstr"
    end
  end...)), ", ")
  trstr = isempty(trmap) ? "" : " || $trmap"
  println(io, "TheoryHom($nX,$nY)($tymap$trstr)")
end 


end # module 