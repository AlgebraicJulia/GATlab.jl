module Backend
export Lvl, ArgLvl, Typ, Trm, TypCon, TrmCon, Axiom, Context, Judgment, Theory, ThEmpty, index, is_context

using StructEquality

using ...Util
using ..Frontend

struct Lvl
  val::UInt64
  function Lvl(i::Int; context=false)
    i > 0 || error("Creating non-positive level $i context $context")
    new(UInt64(i) | (UInt64(context) << 63))
  end
end
"""N is length of theory"""
function Lvl(i::Int, n::Int) 
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
    !is_context(l) || isempty(a) || error("Elements of context are *nullary* type constructors")
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

Base.getindex(t::TheoryMap, i::Int) = t.composites[i]
Base.collect(t::TheoryMap) = collect(t.composites)
Base.length(t::TheoryMap) = length(t.composites)
(t::TheoryMap)(i::Int) = t[i]

"""Map a context in the domain theory into a context of the codomain theory"""
function (f::TheoryMap)(c::Context)
  cc = Context() # codom context, will be iteratively built up 
  for (i,(cname, ctyp)) in enumerate(c)
    new_typ, n_args = f(ctyp.head), f.(ctyp.args)
    println("i $i cname $cname n_args $n_args new_typ $new_typ")
    push!(cc, (cname,new_typ))
  end
  return cc
end

"""
Suppose dom(f) is [X,Y,Z,P,Q] and codom(f) is [X,ϕ,ψ]
suppose we have a term: P(a,q(b,c)) ⊢ a::X,b::Y,c::Z
i.e. 4(6,5(7,8))

f maps {P(x,y) ⊢ x::X,y::Y} 
to ϕ(ψ(y),x)

and {q(u,w) ⊢ u::Y,w::Z} to 
β(w)

We should our term translate first to ϕ(ψ(y),x) 
3(2(5),4)

and then substitute x (i.e. 4) for the mapped first argument 
y (i.e. 5) for f(q(b,c)) i.e. ϕ(ψ(β(c)),x)



"""
function (f::TheoryMap)(t::Trm) 
  println("APPLYING f to $t")
  i_d, i_cd = length.([f.dom,f.codom])
  if t.head > i_d 
    length(t.args) == 0 || error("Context variables have no args")
    println("VARIABLE! f($t) = Trm($(t.head - i_d + i_cd))")
    return Trm(t.head - i_d + i_cd)
  end 
  new_trm, n_args = f(t.head), f.(t.args) # in the translated context
  # the new term is in the context of the term constructor for the head in the codom
  new_trm_j = f.codom[new_trm.head]
  new_trm_arg_inds = [findfirst(==(), new_trm.args)]
  println("new term ctx $(new_trm_j.name) ", new_trm_j.ctx)
  substitute(new_trm, n_args, i_cd)
  
  # println("$t ARGS ", length(n_args), "\n\tn_args $n_args")
  # found = [findfirst(==(a),new_trm.args) for a in n_args]
  # if !isempty(found) println("found $found") end
  # function R(t::Trm) 
  #   println("FIXING $t w/ head $(t.head)")
  #   if t.head > i_cd 
      
  #     return Trm(i_cd + findfirst(==(t),n_args))
  #   else 
  #     Trm(t.head, R.(t.args))
  #   end 
  # end
  # res = R(new_trm)
  # println("f($t) = $res")
  # return res
end 

function substitute(t::Trm, ts::Vector{Trm}, off::Int)
  println("substituting $t (off $off)\n\t with ts $ts")
  if t.head - off > 0 
    return ts[t.head - off ]
  else 
    return Trm(t.head, [substitute(a, ts, off) for a in t.args])
  end
end 

end
