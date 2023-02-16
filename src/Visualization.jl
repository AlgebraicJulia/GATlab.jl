module Visualization
using ..Core 

Base.show(t::AbstractTheory) = """Theory
$(join(type_constructors(t)), "\n")
$(join(term_constructors(t)), "\n")
$(join(axioms(t)), "\n")
"""
Base.show(t::TypeConstructor) = show(sequent(t)) 
Base.show(t::TermConstructor) = show(sequent(t)) 
Base.show(t::Axiom) = show(sequent(t)) 

struct Sequent 
  name::String
  ctx::Vector{Pair{Vector{String}, String}} 
  judgment::String
end 

function show(s::Sequent)
  numerator = join(["($(join(xs, ","))):$t" for (xs,t) in s.ctx], " | ")
  n = maximum(length.([numerator, s.judgment]))
  return join([numerator,repeat("-",n), s.judgment],"\n")
end

"""Convert a type constructor into a context string and a """
function sequent(t::Constructor)
  arg_syms = [show_cons(t.ctx,i,j) for (i,j) in args(t)]
  Sequent(t.name * " introduction", 
          extract_ctx(t.ctx), t.name*"($(join(arg_syms, ","))")
end 

function sequent(t::Axiom)
  t_cons = term_constructors(t)
  t1,t2 = [show_cons(t.ctx,i,j) for (i,j) in [t.lhs,t.rhs]]
  typ = show_type(t.ctx, t.type)
  Sequent(t.name, extract_ctx(t.ctx), "$t1 = $t2 : $typ")
end

"""Gets term constructor by default, term=false to get type constructor"""
function get_cons(t::Theory, lvl::Int,i::Int; term=true)
  if lvl == 0
    return term ? t.term_constructors[i] : t.type_constructors[i]
  else
    return get_cons(t, lvl-1, i)
  end
end

function show_cons(t::Theory, c::Constructor)
  a = isempty(c.args) ? "" : "($(join([show_cons(t,c.args...)],",")))"
  return c.symbol * a
end

show_cons(t::Theory, lvl::Int,i::Int; term=true) = 
  show_cons(t, get_cons(t,lvl,i; term=term))




end # module 