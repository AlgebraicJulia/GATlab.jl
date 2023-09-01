module GATs
export Constant, AlgTerm, AlgType,
  TypeScope, AlgSort, AlgSorts,
  AlgTermConstructor, AlgTypeConstructor, AlgAxiom, sortsignature,
  JudgmentBinding, GATSegment, GAT, sortcheck, allnames, sorts, sortname,
  termcons, typecons, accessors, equations, build_infer_expr, compile

using ..Scopes

using StructEquality

"""
We need this to resolve a mutual reference loop; the only subtype is Constant
"""
abstract type AbstractConstant end

"""
`AlgTerm`

One syntax tree to rule all the terms.
Head reference can be a AlgTermConstructor, Binding{AlgType, Nothing}, AbstractConstant
"""
@struct_hash_equal struct AlgTerm
  head::Union{Reference, AbstractConstant}
  args::Vector{AlgTerm}
  function AlgTerm(head::Union{Reference, AbstractConstant}, args::Vector{AlgTerm}=EMPTY_ARGS)
    new(head, args)
  end
end

const EMPTY_ARGS = AlgTerm[]

AlgTerm(head::Ident, args::Vector{AlgTerm}=EMPTY_ARGS) = AlgTerm(Reference(head), args)

"""
`AlgType`

One syntax tree to rule all the types.
`head` must be reference to a `AlgTypeConstructor`
"""
@struct_hash_equal struct AlgType
  head::Reference
  args::Vector{AlgTerm}
  function AlgType(head::Reference, args::Vector{AlgTerm}=EMPTY_ARGS)
    new(head, args)
  end
end

AlgType(head::Ident, args::Vector{AlgTerm}=EMPTY_ARGS) = AlgType(Reference(head), args)

"""
`Constant`

A Julia value in an algebraic context. Checked elsewhere.
"""
@struct_hash_equal struct Constant
  value::Any
  type::AlgType
end

"""
`AlgSort`

A *sort*, which is essentially a type constructor without arguments
`ref` must be reference to a `AlgTypeConstructor`
"""
@struct_hash_equal struct AlgSort
  ref::Reference
end

AlgSort(i::Ident) = AlgSort(Reference(i))

function AlgSort(c::Context, t::AlgTerm)
  if t.head isa AbstractConstant
    AlgSort(t.head.type.head)
  else
    binding = c[only(t.head)]
    value = getvalue(binding)
    if value isa AlgType
      AlgSort(value.head)
    elseif value isa AlgTermConstructor
      AlgSort(value.type.head)
    else
      error("head of AlgTerm $value is not a term constructor or variable")
    end
  end
end

"""
`Context`

A scope where variables are assigned to `AlgType`s, and no overloading is
permitted.
"""
const TypeScope = Scope{AlgType, Nothing}

"""
`SortContext`

A scope where variables are assigned to `AlgSorts`s, and no overloading is
permitted.
"""
const SortScope = Scope{AlgSort, Nothing}

"""`sortcheck(ctx::Context, t::AlgTerm)`

Throw an error if a the head of an AlgTerm (which refers to a term constructor)
has arguments of the wrong sort. Returns the sort of the term.
"""
function sortcheck(ctx::Context, t::AlgTerm)::AlgSort
  if t.head isa Reference
    judgment = ctx[t.head] |> getvalue
    if judgment isa AlgType
      isempty(t.args) || error("Cannot apply a variable to arguments: $t")
    elseif judgment isa AlgTermConstructor
      argsorts = sortcheck.(Ref(ctx), t.args)
      argsorts == sortsignature(judgment) || error("Sorts don't match")
    else 
      error("Unexpected judgment type $ref for AlgTerm $t")
    end
  elseif t.head isa Constant
  else 
    error("Unexpected head for AlgTerm")
  end
  return AlgSort(ctx, t)
end

"""`sortcheck(ctx::Context, t::AlgType)`

Throw an error if a the head of an AlgType (which refers to a type constructor)
has arguments of the wrong sort.
"""
function sortcheck(ctx::Context, t::AlgType)
  ref = ctx[t.head] |> getvalue
  ref isa AlgTypeConstructor || error("AlgType head must refer to AlgTypeConstructor: $ref")
  argsorts = sortcheck.(Ref(ctx), t.args)
  expected = AlgSort.([a.head for a in getvalue.(ref.args)])
  argsorts == expected || error("Sorts don't match: $argsorts != $expected")
end

"""
`AlgTypeConstructor`

A declaration of a type constructor
"""
@struct_hash_equal struct AlgTypeConstructor
  localcontext::TypeScope
  args::TypeScope
end

"""
`AlgTermConstructor`

A declaration of a term constructor
"""
@struct_hash_equal struct AlgTermConstructor
  localcontext::TypeScope
  args::TypeScope
  type::AlgType
end

sortsignature(tc::Union{AlgTypeConstructor, AlgTermConstructor}) =
  AlgSort.([a.head for a in getvalue.(tc.args)])

"""
`AlgAxiom`

A declaration of an axiom
"""
@struct_hash_equal struct AlgAxiom
  localcontext::TypeScope
  type::AlgType
  equands::Vector{AlgTerm}
end

"""
`Judgment`

A judgment is either a type constructor, term constructor, or axiom; a GAT
is composed of a list of judgments.
"""
const Judgment = Union{AlgTypeConstructor, AlgTermConstructor, AlgAxiom}

"""
`AlgSorts`

A description of the argument sorts for a term constructor, used to disambiguate
multiple term constructors of the same name.
"""
const AlgSorts = Vector{AlgSort}

"""
`JudgmentBinding`

A binding of a judgment to a name and possibly a signature.
"""
const JudgmentBinding = Binding{Judgment, Union{AlgSorts, Nothing}}

"""
`GATSegment`

A piece of a GAT, consisting of a scope that binds judgments to names, possibly
disambiguated by argument sorts.
"""
const GATSegment = Scope{Judgment, Union{AlgSorts, Nothing}}

function allnames(seg::GATSegment; aliases=false)
  names = Symbol[]
  for binding in seg
    judgment = getvalue(binding)
    if judgment isa AlgTermConstructor
      if aliases
        append!(names, getaliases(binding))
      else
        push!(names, nameof(binding))
      end
    elseif judgment isa AlgTypeConstructor
      if aliases
        append!(names, getaliases(binding))
      else
        push!(names, nameof(binding))
      end
      for argbinding in judgment.args
        push!(names, nameof(argbinding))
      end
    end
  end
  names
end

"""
`GAT`

A generalized algebraic theory. Essentially, just consists of a name and a list
of `GATSegment`s, but there is also some caching to make access faster.
Specifically, there is a dictionary to map ScopeTag to position in the list of
segments, and there are lists of all of the identifiers for term constructors,
type constructors, and axioms so that they can be iterated through faster.

GATs allow overloading but not shadowing.
"""
struct GAT <: Context
  name::Symbol
  segments::ScopeList{Judgment, Union{AlgSorts, Nothing}}
  termcons::Vector{Ident}
  typecons::Vector{Ident}
  accessors::Dict{Symbol, Set{Ident}}
  axioms::Vector{Ident}
  function GAT(name::Symbol, segments::Vector{GATSegment})
    termcons = Ident[]
    typecons = Ident[]
    axioms = Ident[]
    # Maps a name of an accessor to the type constructors it appears in
    accessors = Dict{Symbol, Set{Ident}}()
    names = Set{Symbol}()
    for segment in segments
      if !isempty(intersect(keys(segment.names), names))
        error("We do not permit shadowing of names between segments of a GAT")
      end
      union!(names, keys(segment.names))
      for (i, binding) in enumerate(segment)
        x = ident(segment, i)
        judgment = getvalue(binding)
        if judgment isa AlgTermConstructor
          push!(termcons, x)
        elseif judgment isa AlgTypeConstructor
          push!(typecons, x)
          for arg in judgment.args
            if nameof(arg) ∉ keys(accessors)
              accessors[nameof(arg)] = Set{Ident}()
            end
            push!(accessors[nameof(arg)], x)
          end
        else
          push!(axioms, x)
        end
      end
    end
    if !isempty(intersect(keys(accessors), names))
      error("We do not permit the arguments to type constructors to have the same name as term constructors or type constructors")
    end
    new(name, ScopeList(segments), termcons, typecons, accessors, axioms)
  end

  # This could be faster, but it's not really worth worrying about
  function GAT(name::Symbol, parent::GAT, newsegment::GATSegment)
    GAT(name, [parent.segments.scopes..., newsegment])
  end
end

Base.nameof(theory::GAT) = theory.name
termcons(theory::GAT) = theory.termcons
typecons(theory::GAT) = theory.typecons
accessors(theory::GAT) = theory.accessors
sorts(theory::GAT) = AlgSort.(theory.typecons)

Scopes.getscopes(c::GAT) = getscopes(c.segments)

Scopes.scopelevel(c::GAT, t::ScopeTag) = scopelevel(c.segments, t)
Scopes.scopelevel(c::GAT, s::Symbol) = scopelevel(c.segments, s)

Base.length(c::GAT) = length(c.segments)
Base.getindex(c::GAT, x::Ident) = getindex(c.segments, x)
Base.getindex(c::GAT, i::Int) = getindex(c.segments, i)

Scopes.ident(c::GAT, level::Int; name=nothing, scopelevel::Union{Int, Nothing}=nothing) =
  ident(c.segments, level; name, scopelevel)

Scopes.ident(c::GAT, name::Symbol; sig=nothing, scopelevel::Union{Int, Nothing}=nothing) =
  ident(c.segments, name; sig, scopelevel)

function allnames(theory::GAT; aliases=false)
  vcat(allnames.(theory.segments; aliases)...)
end

function sortname(theory::GAT, type::AlgType)
  canonicalize(theory, only(type.head))
end

## Equations

struct AccessorApplication
  accessor::Ident
  to::Union{Ident, AccessorApplication}
end

const InferExpr = Union{Ident, AccessorApplication}

function build_infer_expr(theorymodule, e::InferExpr)
  if e isa Ident
    nameof(e)
  else
    Expr(:call, :($theorymodule.$(nameof(e.accessor))), build_infer_expr(theorymodule, e.to))
  end
end

""" Implicit equations defined by a context.

This function allows a generalized algebraic theory (GAT) to be expressed as
an essentially algebraic theory, i.e., as partial functions whose domains are
defined by equations.

References:
 - (Cartmell, 1986, Sec 6: "Essentially algebraic theories and categories with
    finite limits")
 - (Freyd, 1972, "Aspects of topoi")

This function gives expressions for computing each of the elements of `context`
  from the `args`, as well as checking that the args are well-typed.

Example:
> equations({f::Hom(a,b), g::Hom(b,c)}, {a::Ob, b::Ob, c::Ob}, ThCategory)
ways_of_computing = Dict(a => [dom(f)], b => [codom(f), dom(g)], c => [codom(g)],   
                         f => [f], g => [g])

Algorithm:

Start from the arguments. We know how to compute each of the arguments; they are
given. Each argument tells us how to compute other arguments, and also elements
of the context
"""
function equations(args::TypeScope, localcontext::TypeScope, theory::GAT)
  ways_of_computing = Dict{Ident, Set{InferExpr}}()
  to_expand = Pair{Ident, InferExpr}[x => x for x in idents(args)]

  context = ScopeList([args, localcontext])
   
  while !isempty(to_expand)
    x, expr = pop!(to_expand)
    if !haskey(ways_of_computing, x)
      ways_of_computing[x] = Set{InferExpr}()
    end
    push!(ways_of_computing[x], expr)

    xtype = getvalue(context[x])
    xtypecon = getvalue(theory[xtype.head])

    for (i, arg) in enumerate(xtype.args)
      if arg.head isa Constant
        continue
      elseif first(arg.head) ∈ theory
        continue
      else
        @assert first(arg.head) ∈ context
        a = ident(xtypecon.args, i)
        y = first(arg.head)
        expr′ = AccessorApplication(a, expr)
        push!(to_expand, y => expr′)
      end
    end
  end
  ways_of_computing
end

function compile(theorymodule, expr_lookup::Dict{Reference}, term::AlgTerm)
  if term.head isa Constant
    term.head.value
  else
    if haskey(expr_lookup, term.head)
      expr_lookup[term.head]
    else
      Expr(
        :call,
        :($theorymodule.$(nameof(only(term.head)))),
        AlgTerm[compile(theorymodule, expr_lookup, arg) for arg in term.args]
      )
    end
  end
end

end
