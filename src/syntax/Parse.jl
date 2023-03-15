module Parse
export @theory, @theorymap, @term

using ...Util.Lists
using ..Frontend
import ..Backend

using MLStyle
using StructEquality

@struct_hash_equal struct SymExpr
  head::Symbol
  args::Vector{SymExpr}
  function SymExpr(head::Symbol, args::Vector=SymExpr[])
    new(head, args)
  end
end

head(e::SymExpr) = e.head

abstract type DeclBody end

struct NewTerm <: DeclBody
  head::Symbol
  args::Vector{Symbol}
  type::SymExpr
end

@as_record NewTerm

struct NewType <: DeclBody
  head::Symbol
  args::Vector{Symbol}
end

@as_record NewType

struct NewAxiom <: DeclBody
  lhs::SymExpr
  rhs::SymExpr
  type::SymExpr
end

@as_record NewAxiom

struct Declaration
  body::DeclBody
  context::Vector{Pair{Symbol, SymExpr}}
end

const Expr0 = Union{Symbol, Expr}

function parse_args(e::Expr0)
  @match e begin
    (name::Symbol) => (name, Expr0[])
    :($(name::Symbol)($(args...))) => (name, Expr0[args...])
    _ => error("Could not parse $e as an application of a head to arguments")
  end
end

function parse_symexpr(e::Expr0)
  (name, args) = parse_args(e)
  SymExpr(name, parse_symexpr.(args))
end

function Base.show(io::IO, m::MIME"text/plain", e::SymExpr)
  print(io, string(e.head))
  if length(e.args) != 0
    print(io, "(")
    for arg in e.args[1:end-1]
      show(io, m, arg)
      print(io, ",")
    end
    show(io, m, e.args[end])
    print(io, ")")
  end
end

function parse_declbody(e::Expr0)
  @match e begin
    :($expr :: TYPE) => NewType(parse_args(expr)...)
    :($expr :: $type) => NewTerm(parse_args(expr)..., parse_symexpr(type))
    :($lhs == $rhs :: $type) => NewAxiom(parse_symexpr(lhs), parse_symexpr(rhs), parse_symexpr(type))
    _ => error("Could not parse declaration head $e")
  end
end

function parse_decl(e::Expr)
  @match e begin
    :($body ⊣ [$(bindings...)]) =>
      Declaration(
        parse_declbody(body),
        parse_binding.(bindings)
      )
    _ => error("Could not parse declaration $e")
  end
end

function parse_binding(binding::Expr)
  @match binding begin
    :($(head::Symbol)::$(type::Expr0)) => (head => parse_symexpr(type))
    _ => error("could not parse binding $binding")
  end
end

function lookup_sym(context::Context, sym::Symbol)
  name = Name(sym)
  for (i, judgment) in enumerate(reverse(context))
    if nameof(judgment) == name
      return i
    end
  end
  throw(KeyError(sym))
end

function construct_type(context::Context, e::SymExpr)
  head = lookup_sym(context, e.head)
  Typ(head, construct_term.(Ref(context), e.args))
end

function construct_term(context::Context, e::SymExpr)
  head = lookup_sym(context, e.head)
  Trm(head, construct_term.(Ref(context), e.args))
end

function construct_ext(context::Context, symext::Vector{Pair{Symbol, SymExpr}})
  foldl(
    (ext, p) -> snoc(
      ext,
      Judgment(
        Name(p[1]),
        Bwd{Judgment}(),
        TrmCon(construct_type(vcat(context, ext), p[2]))
      )
    ),
    symext;
    init=Bwd{Judgment}()
  )
end

function construct_judgment(context::Context, decl::Declaration)
  ext = construct_ext(context, decl.context)
  headctx = vcat(Bwd(context), ext)
  (name, head) = @match decl.body begin
    NewTerm(head, args, type) =>
      (
        Name(head),
        TrmCon(construct_type(headctx, type), lookup_sym.(Ref(headctx), args))
      )
    NewType(head, args) =>
      (
        Name(head),
        TypCon(lookup_sym.(Ref(headctx), args))
      )
    NewAxiom(lhs, rhs, type) =>
      (
        Anon(),
        Axiom(
          construct_type(headctx, type),
          construct_term.(Ref(headctx), [lhs, rhs])
        )
      )
  end
  Judgment(name, ext, head)
end

function theory_impl(parent::Backend.Theory, name::Symbol, lines::Vector)
  context = foldl(
    (context, line) -> snoc(context, construct_judgment(context, parse_decl(line))),
    lines; init=parent.orig.context
  )
  Backend.Theory(Theory(Name(name), context))
end

macro theory(head, body)
  (name, parent) = @match head begin
    :($(name::Symbol) <: $(parent::Symbol)) => (name, parent)
    _ => error("expected head of @theory macro to be in the form name <: parent")
  end
  lines = @match body begin
    Expr(:block, lines...) => filter(line -> typeof(line) != LineNumberNode, lines)
    _ => error("expected body of @theory macro to be a block")
  end
  esc(
    quote
      $name = $(GlobalRef(Parse, :theory_impl))($parent, $(Expr(:quote, name)), $lines)
    end
  )
end

"""
@theory ThSet <: Empty begin
  Ob::TYPE ⊣ []
end

@theory ThGraph <: ThSet begin
  Hom(x,y)::TYPE ⊣ [a::Ob, b::Ob]
end

@theory LawlessCategory <: Graph begin
  compose(f,g)::Hom(a,c) ⊣ [a::Ob, b::Ob, c::Ob, f::Hom(a,b), g::Hom(b,c)]
end
"""

function parse_mapping(expr)
  @match expr begin
    :($lhs => $rhs) => (parse_symexpr(lhs) => parse_symexpr(rhs))
    _ => error("illformed line in @gatmap")
  end
end

function onlydefault(xs; default=nothing)
  if length(xs) == 1
    xs[1]
  else
    default
  end
end

function theorymap_impl(dom::Theory, codom::Theory, lines::Vector)
  mappings = parse_mapping.(lines)
  mappings = Bwd(onlydefault(filter(m -> Name(m[1].head) == j.name, mappings)) for j in dom.context)
  composites = foldl(zip(mappings, dom.context); init=Bwd{Composite}()) do composites, (mapping, judgment)
    snoc(composites, make_composite(codom.context, judgment, mapping))
  end
  TheoryMap(dom, codom, composites)
end

function make_composite(
  codom::Context,
  judgment::Judgment,
  mapping::Union{Pair{SymExpr, SymExpr}, Nothing}
)
  if isnothing(mapping)
    typeof(judgment.head) == Axiom || error("must provide a mapping for $(judgment.name)")
    return nothing
  end
  lhs, rhs = mapping
  all(length(arg.args) == 0 for arg in lhs.args) || error("left side of mapping must be a flat expression")
  length(lhs.args) == arity(judgment.head) || error("wrong number of arguments for $(judgment.name)")
  names = Dict(zip(judgment.head.args, Name.(head.(lhs.args))))
  renamed_ctx = Bwd{Judgment}(map(zip(reverse(eachindex(judgment.ctx)), judgment.ctx)) do (i,j)
    newname = get(names, i, Anon())
    Judgment(newname, j.ctx, j.head)
  end)
  ctx = vcat(codom, renamed_ctx)
  if typeof(judgment.head) == TrmCon
    construct_term(ctx, rhs)
  else
    construct_type(ctx, rhs)
  end
end

macro theorymap(head, body)
  dom, codom = @match head begin
    Expr(:->, dom, Expr(:block, _, codom)) => (dom, codom)
    _ => error("expected head of @theorymap to be of the form `dom -> codom`")
  end
  lines = @match body begin
    Expr(:block, lines...) => filter(line -> typeof(line) != LineNumberNode, lines)
    _ => error("expected body of @theorymap to be a block")
  end
  esc(
    quote
      $(GlobalRef(Parse, :theorymap_impl))($dom, $codom, $lines)
    end
  )
end

function term_impl(theory::Backend.Theory, expr::Expr0)
  Backend.levelize(
    construct_term(theory.orig.context, parse_symexpr(expr)),
    length(theory.judgments)
  )
end

macro term(theory, expr)
  esc(:($(GlobalRef(Parse, :term_impl))($theory, $(Expr(:quote, expr)))))
end

end
