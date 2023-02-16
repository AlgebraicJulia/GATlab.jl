module Core
export TermCon, TypeCon, TermInContext, TypeInContext, Axiom,
       EmptyTheory, TheoryExt, Theory, 
       TheoryExtType, TheoryExtTerm, TheoryExtAxiom,
       typecons, termcons, axioms, args, head
# Terms
#######

abstract type InContext end 
abstract type Constructor end 
abstract type Theory end


const DeBruijn = Tuple{Int,Int}

"""
head - indexes term constructors in a certain theory, seen as a context
args - 
"""
struct TermInContext <: InContext
  head::DeBruijn # debruijn index into the term context
  args::Vector{TermInContext}
  TermInContext(h,a=TermInContext[]) = new(h,a)
end

struct TypeInContext <: InContext
  head::DeBruijn # debruijn index into the type context
  args::Vector{TermInContext}
  TypeInContext(h,a=TermInContext[]) = new(h,a)
end

head(x::InContext) = x.head
args(x::InContext) = x.args

# Judgments
############

"""
A type constructor for some theory of T

ctx  - a theory that is a decendent of the parent of T 
name - just documentation (and for rendering)
args - indexing all the term constructors in ctx
       this should be sufficient to type infer everything in ctx
"""
struct TypeCon <: Constructor
  ctx::Theory
  name::Symbol # JUST DOCUMENTATION
  args::Vector{DeBruijn} 
  TypeCon(c,n,a=DeBruijn[]) = new(c,n,a)
end

"""
A term constructor for some theory of T

ctx  - a theory that is a decendent of the parent of T 
name - just documentation (and for rendering)
typ  - output type of applying the term constructor
args - indexing all the term constructors in ctx
       this should be sufficient to type infer everything in ctx
"""
struct TermCon <: Constructor
  ctx::Theory
  name::Symbol
  typ::TypeInContext
  args::Vector{DeBruijn}
  TermCon(c,n,t,a=DeBruijn[]) = new(c,n,t,a)
end

args(x::Constructor) = x.args

struct Axiom <: Constructor
  ctx::Theory
  name::Symbol
  type::TypeInContext
  rhs::TermInContext
  lhs::TermInContext
end

# Theories
###########


struct EmptyTheory <: Theory end 

struct TheoryExt <: Theory
  parent::Theory
  typecons::Vector{TypeCon}
  termcons::Vector{TermCon}
  axioms::Vector{Axiom}
  function TheoryExt(parent,typecons,termcons,axioms)
    for tc in termcons ∪ typecons
      # parent ∉ ancestors(tc.ctx) || error("")
    end 
    new(parent,typecons,termcons,axioms)
  end
end

TheoryExtType(p,tc::Vector{TypeCon}) =
  TheoryExt(p,tc,TermCon[],Axiom[])

TheoryExtTerm(p,tc::Vector{TermCon}) =
  TheoryExt(p,TypeCon[],tc,Axiom[])

TheoryExtAxiom(p,ax::Vector{Axiom}) = 
  TheoryExt(p,TypeCon[],TermCon[],ax)

"""List all type/term constructors"""
typecons(::EmptyTheory) = []
typecons(t::TheoryExt) = vcat([t.typecons], typecons(t.parent))
termcons(::EmptyTheory) = []
termcons(t::TheoryExt) = vcat([t.termcons], termcons(t.parent))
axioms(::EmptyTheory) = []
axioms(t::TheoryExt) = vcat([t.axioms], axioms(t.parent))

parent(::EmptyTheory) = EmptyTheory()
parent(t::TheoryExt) = t.parent


end # module
