module GATs
export DeBruijn, TermCon, TypeCon, TermInContext, TypeInContext, Axiom,
       ThEmpty, TheoryExt, Theory, Context,
       TheoryExtType, TheoryExtTerm, TheoryExtAxiom,
       typecons, termcons, axioms, args, headof, name, dom, codom, ctx

using StructEquality

# Terms
#######

abstract type InContext end 
abstract type Judgment end 
abstract type Constructor <: Judgment end 
abstract type Theory end

const DeBruijn = Tuple{Int,Int}

"""
head - indexes term constructors in an (implicit) theory
args - arguments that the term constructor is applied to
"""
@struct_hash_equal struct TermInContext <: InContext
  head::DeBruijn # debruijn index into the term context
  args::Vector{TermInContext}
  TermInContext(h,a=TermInContext[]) = new(h,a)
end

@struct_hash_equal struct TypeInContext <: InContext
  head::DeBruijn # debruijn index into the type context
  args::Vector{TermInContext}
  TypeInContext(h,a=TermInContext[]) = new(h,a)
end

headof(x::InContext) = x.head
args(x::InContext) = x.args
arity(x::InContext) = length(args(x))

# Offset the depth of the index
Base.:(+)(x::T, n::Int) where T<:InContext = let (h1,h2) = headof(x);
                                             T((h1+1,h2),args(x).+n) end
# Context 
#########

"""
A context is an extension of a theory that adds only nullary term constructors.
The depth parameter indicates what theory to interpret as being extended.
"""
@struct_hash_equal struct Context 
  depth::Int
  codom::Theory
  function Context(d::Int,e::Theory) 
    t = parent(e,d)
    is_context(e,t;check=true)
    return new(d,e)
  end
end
Context(t::Theory) = Context(0, t)
Context(c::Context) = c

dom(c::Context) = parent(c.codom,c.depth) 
codom(c::Context) = c.codom
Base.length(c::Context) = c.depth
Base.collect(t::Context) = reverse(ancestors(codom(t))[1:t.depth])

# Judgments
############

"""
A type constructor for some theory of T

ctx  - a context whose base theory is the parent of the theory of this typecon
name - just documentation (and for rendering)
args - indexing all the term constructors in ctx
       this should be sufficient to type infer everything in ctx
"""
struct TypeCon <: Constructor
  ctx::Context
  name::Symbol
  args::Vector{DeBruijn} 
  TypeCon(c,n,a=DeBruijn[]) = new(Context(c),n,a)
end

Base.:(==)(x::TypeCon, y::TypeCon) = x.args == y.args && x.ctx == y.ctx 
Base.hash(x::TypeCon, h::UInt64) = hash(x.ctx, hash(x.args, h))

"""
A term constructor for some theory of T

ctx  - a theory that is a decendent of the parent of T 
name - just documentation (and for rendering)
typ  - output type of applying the term constructor
args - indexing all the term constructors in ctx
       this should be sufficient to type infer everything in ctx
"""
struct TermCon <: Constructor
  ctx::Context
  name::Symbol 
  typ::TypeInContext
  args::Vector{DeBruijn}
  TermCon(c,n,t,a=DeBruijn[]) = new(Context(c),n,t,a)
end

Base.:(==)(x::TermCon, y::TermCon) =   
  x.typ == y.typ && x.args == y.args && x.ctx == y.ctx
Base.hash(x::TermCon, h::UInt64) = hash(x.ctx, hash(x.typ, hash(x.args, h)))

args(x::Constructor) = x.args
arity(x::Constructor) = length(args(x))

Context(t::Theory, tc::Union{TermCon, AbstractVector{TermCon}}; name="") = 
  Context(1, TheoryExtTerm(t,tc;name=name))
Context(c::Context,tc::Union{TermCon, AbstractVector{TermCon}}; name="") = 
  Context(1+c.depth, TheoryExtTerm(codom(c),tc;name=name, check_ctx=false))

struct Axiom <: Judgment
  ctx::Context
  name::Symbol
  type::TypeInContext
  rhs::TermInContext
  lhs::TermInContext
  Axiom(c,n,t,r,l) = new(Context(c),n,t,r,l)
end

Base.:(==)(x::Axiom, y::Axiom) =   
  x.type == y.type && x.lhs == y.lhs && x.rhs == y.rhs && x.ctx == y.ctx
Base.hash(x::Axiom, h::UInt64) = 
  hash(x.ctx, hash(x.type, hash(x.lhs, hash(x.rhs, h))))

ctx(x::Judgment) = x.ctx
name(x::Judgment) = x.name 

# Theories
###########

"""
A theory is a sequence of judgments. However, some of these judgments 
do not depend on each other and thus can be considered in the same 
"level" of the hierarchy. 

Presentations of theories can be syntactically different while being 
semantically equivalent. For example, ThEmpty cannot be equal to an
empty TheoryExtension of ThEmpty, even though both 'are' ThEmpty.

Some Gatlab machinery will at first demand presentations to be equal (e.g. 
morphism composition); as we implement/improve inference, this can be relaxed.
"""
@struct_hash_equal struct EmptyTheory <: Theory end 
const ThEmpty = EmptyTheory()

name(::EmptyTheory) = "Empty" 
Base.parent(::EmptyTheory) = ThEmpty
typecons(::EmptyTheory) = []
termcons(::EmptyTheory) = []
axioms(::EmptyTheory) = []
ancestors(::EmptyTheory) = [ThEmpty]


"""
Name     - just documentation
Parent   - the theory being extended
typecons - new type constructors, e.g. Hom(a,b):TYPE ⊣ (a, b):Ob
termcons - new term constructors, e.g. (f⋅g):Hom(a,c) ⊣ abc:Ob, f:Hom(a,b), ...
axioms   - new axioms e.g. ((f ⋅ g) ⋅ h == (f ⋅ (g ⋅ h)) :: Hom(a,d)) ⊣ ...
check_ctx- whether or not to enforce that the context of judgments is the parent 
           theory. We generally want this to be the case, except in the case of 
           building up a context iteratively, e.g. T ⊂ C1 ⊂ C2, in which case 
           we want the C2 to be a context of depth 2 even though its parent 
           theory is C1).
"""
struct TheoryExt <: Theory
  name::Symbol
  parent::Theory
  typecons::Vector{TypeCon}
  termcons::Vector{TermCon}
  axioms::Vector{Axiom}
  function TheoryExt(name,parent,typecons,termcons,axioms; check_ctx=true)
    for c in [termcons..., typecons..., axioms...]
      # Check parent ∈ ancestors(ctx(c)) + only nullary term constructors added
      e = "Bad context for $c in $name w/ parent $parent"
      !check_ctx || dom(ctx(c)) == parent || error(e)
    end
    return new(name,parent,typecons,termcons,axioms)
  end
end

rename(t::TheoryExt,n::Symbol) = 
  TheoryExt(n,t.parent,t.typecons,t.termcons,t.axioms)

"""Chain of ancestors, ending in ThEmpty"""
ancestors(t::TheoryExt) = [t, ancestors(parent(t))...]

"""
The most recent common ancestor of two theories. Always exists due to ThEmpty.
"""
meet(::EmptyTheory,::Theory) = ThEmpty 
meet(::Theory,::EmptyTheory) = ThEmpty 
function meet(x::TheoryExt,y::TheoryExt) 
  y_downset = Set(ancestors(y))
  while true
    if x ∈ y_downset 
      return x
    else 
      x = parent(x)
    end
  end 
end


TheoryExtType(p,tc::AbstractVector{TypeCon}; name="") =
  TheoryExt(Symbol(name),p,tc,TermCon[],Axiom[])

TheoryExtTerm(p,tc::AbstractVector{TermCon}; name="", check_ctx=false) =
  TheoryExt(Symbol(name),p,TypeCon[],tc,Axiom[];check_ctx=check_ctx)

TheoryExtAxiom(p,ax::AbstractVector{Axiom}; name="") = 
  TheoryExt(Symbol(name),p,TypeCon[],TermCon[],ax)

TheoryExtType(p,  tc::TypeCon; name="") = TheoryExtType(p,[tc];name=name)
TheoryExtTerm(p,  tc::TermCon; name="", check_ctx=false) = TheoryExtTerm(p,[tc];name=name,check_ctx=check_ctx)
TheoryExtAxiom(p, ax::Axiom;   name="") = TheoryExtAxiom(p,[ax];name=name)

Base.:(==)(x::TheoryExt, y::TheoryExt) = (x.termcons == y.termcons 
  && x.typecons == y.typecons && x.axioms == y.axioms && x.parent == y.parent)
Base.hash(x::TheoryExt, h::UInt64) = 
  hash(x.parent, hash(x.typecons, hash(x.termcons, hash(x.axioms,h))))

name(x::TheoryExt) = x.name 
typecons(t::TheoryExt) = t.typecons
termcons(t::TheoryExt) = t.termcons
axioms(t::TheoryExt) = t.axioms

"""
List all type/term constructors along with the theory when they are introduced

E.g. typecons(Th) == [..., ThGrph=>[Hom],ThSet=>[Ob], ThEmpty=>[]]
"""
all_typecons(t::Theory) = [t=>typecons(t) for t in ancestors(t)] # vcat([t=>t.typecons], typecons(t.parent))
all_termcons(t::Theory) = [t=>termcons(t) for t in ancestors(t)]# vcat([t=>t.termcons], termcons(t.parent))
all_axioms(t::Theory) = [t=>axioms(t) for t in ancestors(t)] # vcat([t=>t.axioms], axioms(t.parent))

"""Traverse linked list of theory extensions"""
Base.parent(t::TheoryExt) = t.parent
function Base.parent(t::Theory, i::Int) 
  if     i == 0 return t 
  elseif i > 0  return parent(parent(t), i - 1)
  else          error("Cannot call parent with negative value")
  end
end

"""
Gets term constructor by default, term=false to get type constructor
"""
function debruijn_to_cons(t::TheoryExt, lvl::Int,i::Int; term=true)
  if lvl == 0
    return term ? t.termcons[i] : t.typecons[i]
  else
    return debruijn_to_cons(t.parent, lvl-1, i; term=term)
  end
end

"""
Checks whether a theory can be thought of as a context for another.
If it is, return a list of indices of the new term constructors.
Otherwise, return nothing.
"""  
is_context(::EmptyTheory, ::EmptyTheory; check=false) = DeBruijn[] 
is_context(::EmptyTheory, t::TheoryExt; check=false) = 
  check ? error("Empty is not a context for TheoryExt $(name(t))") : nothing
function is_context(X::TheoryExt, Y::Theory; check=false) 
  # show(stdout,"text/plain",X)
  if X == Y return DeBruijn[] end 
  parent_ctx = is_context(parent(X), Y; check=check)
  if isnothing(parent_ctx) 
    return nothing
  elseif !isempty(X.typecons) 
    return check ? error("Non-empty type constructors") : nothing
  elseif !isempty(X.axioms) 
    return check ? error("Non-empty axioms") : nothing
  elseif any(tc -> !isempty(tc.args), X.termcons)
    return check ? error("Non nullary term constructors") : nothing
  end
  return vcat([(i+1,j) for (i,j) in parent_ctx], 
              [(0,i) for i in 1:length(X.termcons)])
end

# Theory Morphisms
##################
"""
Functionally, a proof certifies that two terms are equal in a theory.

Once we have more idea what concrete structure non-trivial proofs will take, 
related to e-graphs, it will become clear how it is we compose proofs when 
composing theory morphisms.
"""
abstract type Proof end
struct SorryProof <: Proof end
const Sorry = SorryProof()
compose(::SorryProof, ::Proof) = Sorry 
compose(::Proof, ::SorryProof) = Sorry 

"""
These are called "interpretations" by Cartmell and "views" by MMT. They  
induce a function f, which converts concrete types/terms in the domain X into
concrete types/terms in codomain Y. The most practical property of theory 
morphisms is that, for every derived rule in X, f(X) is a derived rule in Y.

The required data is 
 1. an assignment of X's TYPEs in the domain to TYPEs in Y
 2. an assignment of X's term cons to expressions in a context of Y

The properties this should satisfy are:

If   a:A ...    in X then     f(a):f(A) ...     is a type constructor in Y
  ------------             ------------------    (up to provable equality)
    T : TYPE                  f(T) : TYPE

If  a:A ...    in X then     f(a):f(A) ...         is a term constructor in Y
  -----------            ---------------------      (up to provable equality)
  ψ(a,...) : B           f(ψ)(f(a),...) : f(B)

If a:A ...    in X then    f(a):f(A) ...     is *provable* in Y
 -----------            -------------------
  t₁=t₂ : B              f(t₁)=f(t₂) : f(B)

As optional data to the morphism, one can attach proofs that witness this last 
point.
"""
abstract type TheoryHom end 
@struct_hash_equal struct EmptyTheoryHom <: TheoryHom
  codom::Theory 
end

"""
For theories that are structured in a linked-list style (with an explicit
parent X′ ↪ X, rather than all at once), a theory morphism can define 
assignments for X's additional content and include a theory morphism X′ → Y.

When Cartmell defines the category GAT (of theories and theory morphisms), 
two theory morphisms F,G are considered equivalent if for all introductory rules
in the domain X, F(X) ≡ G(X) is derivable in Y.

name    - Just for documentation
parent  - Morphism to codom from the theory that the dom extends
(co)dom - domain and codomain of theory morphism
typemap - Refer to type constructors in the codom via DeBruijn indices
termmap - Terms in the (translated) context of the domain's term constructors
axmap   - Proofs that F(a)=F(b) (in codomain) for each axiom a=b in the domain.
"""
@struct_hash_equal struct TheoryHomExt <: TheoryHom
  name::Symbol
  parent::TheoryHom 
  dom::TheoryExt
  codom::Theory
  typemap::Vector{DeBruijn}
  termmap::Vector{TermInContext}
  axmap::Vector{Proof}
  """Apply very basic checks that can be done purely syntactically"""
  function TheoryHomExt(p,d,c,ty=[],trm=[],ax_=nothing,n="")
    ax = isnothing(ax_) ? fill(Sorry, length(d.axioms)) : ax_
    dom(p) == parent(d) || error("Dom of parent of hom must be parent of dom")
    codom(p) == c || error("Codoms of hom and its parent must be the same.")
    length(ty) == length(d.typecons) || error("One type assignment per typecon")
    length(trm) == length(d.termcons) || error("One term assignment per termcon")
    length(ax) == length(d.axioms) || error("One proof per axiom")
    return new(Symbol(n), p,d,c,ty,trm,ax)
  end
end

Base.parent(f::EmptyTheoryHom) = f
Base.parent(f::TheoryHomExt) = f.parent
name(f::EmptyTheoryHom) = name(codom(f))
name(f::TheoryHomExt) = f.name
dom(::EmptyTheoryHom) = ThEmpty 
dom(f::TheoryHomExt) = f.dom
codom(f::TheoryHom) = f.codom 
typemap(::EmptyTheoryHom) = DeBruijn[]
typemap(f::TheoryHomExt) = f.typemap
termmap(::EmptyTheoryHom) = Pair{Context,TermInContext}[]
termmap(f::TheoryHomExt) = f.termmap
axmap(::EmptyTheoryHom) = Proof[]
axmap(f::TheoryHomExt) = f.axmap

"""Send an index (referring to a type constructor) in dom to one in codom"""
function typemap(f::TheoryHomExt, d::DeBruijn)
  d1,d2 = d 
  if d1 == 0
    return typemap(f)[d2]
  else 
    return typemap(parent(f), (d1-1, d2))
  end
end 


"""
Take theory homs A -> B and B -> C and produce a theory hom A -> C
"""
function compose(f::TheoryHomExt, g::TheoryHomExt) 
  (X, Y), (Y′,Z) = dom.([f,g]), codom.([f,g]) 
  # is this too strict - do we want them to be equal up to provable eq?
  Y == Y′ || error("Cannot compose $f $g")
  error("NOTIMPLEMENTED: Need to compute ty, trm, and ax")
  new_name = "$(name(f)) ⋅ $(name(g))"
  ty = [typemap(g, ij) for ij in typemap(f)]
  ty = map(termmap(f)) do x 
  end
  ty = [Sorry for _ in axmap(f)]
  TheoryHomExt(compose(parent(f), g), X, Z, ty, trm, ax, new_name)
end 

compose(f::TheoryHom, g::EmptyTheoryHom) = 
  codom(f) == ThEmpty : g : error("Cannot compose $f $g")
compose(f::EmptyTheoryHom, g::TheoryHom) = 
  codom(f) == dom(g) : EmptyTheoryHom(codom(g)) : error("Cannot compose $f $g")


"""
Given a theory hom F: X -> Y and an extension of theory X that only adds 
nullary term constructors.

E.g. X is ThCategory + initial/terminal objects 0,1::Ob 
  a::Ob | (f,g):Hom(codom(id(0)⋅id(0)), 1) ... 

This uses the morphism to produce a context (of theory Y).

x:F(C) | (a₁,a₂):F(A)(x, F(S(0) + 0)) ... 

   X ↪ X₁ ↪ X₂ ↪ X₃
 F ↓   
   Y ↪ Y₁ ↪ Y₂ ↪ Y₃

"""
function (f::TheoryHomExt)(t::Context)
  error("NOT IMPLEMENTED YET")
  dom(t) == dom(f) || error("Can not lift context: domains do not agree")
  n_f = name(f)
  new_ctx = Context(0,codom(f)) # initialize result
  # Create a corresponding extension Yᵢ for each extension Xᵢ in context.
  for (i, ext) in enumerate(collect(t))
    new_terms = map(termcons(ext)) do tc # term constructor in X 
      isempty(args(tc)) || error("Context only adds nullary term constructors")
      f_c = f(ctx(tc))
      type_depth, type_ind = tc.typ.head
      ty_head = typemap(f,(type_depth - i, type_ind))
      ty = TypeInContext(ty_head,map(tc.type.args) do t_arg 
        f(t_arg)
      end)
      TermCon(f_c, "$n_f($(name(tc)))", ty)
    end 
    new_ctx = Context(i, TheoryExtTerm(codom(new_ctx), new_terms; name="$n_f $i"))
  end 
  return new_ctx
end 




""" 
Cartmell defines a category of "contexts and realizations" for a given theory U. 
Given that our contexts are implemented as theory extensions, this precisely 
corresponds to a coslice category of the above category of theories,
restricted to nullary termcon theory extensions.

     U
    ↙ ↘
Ctx₁ → Ctx₂
"""


# Type inference/unification
############################
# TBD: this is undecidable in general modulo equations -- we will need to 
# infer types via e-graphs.

end # module
