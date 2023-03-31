module Parse
export @theory, @theorymap, @term, @context

using ..Expressions
using ...Util

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
  name::Name
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

function reassociate_decl(e)
  @match e begin
    :($name := $lhs == $rhs :: $typ ⊣ $ctx) => :(($name := ($lhs == $rhs :: $typ)) ⊣ $ctx)
    :($lhs == $rhs :: $typ ⊣ $ctx) => :(($lhs == $rhs :: $typ) ⊣ $ctx)
    e => e
  end
end

function parse_decl(e::Expr)
  @match reassociate_decl(e) begin
    :($body ⊣ [$(bindings...)]) =>
      Declaration(
        parse_declbody(body),
        parse_binding.(bindings)
      )
    body => Declaration(parse_declbody(body), Pair{Symbol, SymExpr}[])
    _ => error("Could not parse declaration $e")
  end
end

function parse_declbody(e::Expr0)
  @match e begin
    :($expr :: TYPE) => NewType(parse_args(expr)...)
    :($expr :: $type) => NewTerm(parse_args(expr)..., parse_symexpr(type))
    :($lhs == $rhs :: $type) =>
      NewAxiom(parse_symexpr(lhs), parse_symexpr(rhs), parse_symexpr(type), Anon())
    :($name := ($lhs == $rhs :: $type)) =>
      NewAxiom(parse_symexpr(lhs), parse_symexpr(rhs), parse_symexpr(type), Name(name))
    _ => error("Could not parse declaration head $e")
  end
end

function parse_binding(binding::Expr)
  @match binding begin
    :($(head::Symbol)::$(type::Expr0)) => (head => parse_symexpr(type))
    _ => error("could not parse binding $binding")
  end
end

function construct_typ(fc::FullContext, e::SymExpr)
  head = lookup(fc, Name(e.head))
  Typ(head, construct_trm.(Ref(fc), e.args))
end

function construct_trm(fc::FullContext, e::SymExpr)
  head = lookup(fc, Name(e.head))
  Trm(head, construct_trm.(Ref(fc), e.args))
end

function construct_context(judgments::Vector{Judgment}, symctx::Vector{Pair{Symbol, SymExpr}})
  c = Context()
  fc = FullContext(judgments, c)
  for (n, symtyp) in symctx
    push!(c.ctx, (Name(n), construct_typ(fc, symtyp)))
  end
  c
end

function construct_judgment(judgments::Vector{Judgment}, decl::Declaration)
  context = construct_context(judgments, decl.context)
  fc = FullContext(judgments, context)
  (name, head) = @match decl.body begin
    NewTerm(head, args, type) =>
      (
        Name(head),
        TrmCon(lookup.(Ref(fc), args), construct_typ(fc, type))
      )
    NewType(head, args) =>
      (
        Name(head),
        TypCon(lookup.(Ref(fc), args))
      )
    NewAxiom(lhs, rhs, type, name) =>
      (
        name,
        Axiom(
          construct_typ(fc, type),
          construct_trm.(Ref(fc), [lhs, rhs])
        )
      )
  end
  Judgment(name, head, context)
end

function theory_impl(parent::Theory, name::Symbol, lines::Vector)
  judgments = copy(parent.judgments)
  for line in lines
    push!(judgments, construct_judgment(judgments, parse_decl(line)))
  end
  Theory(Name(name), judgments)
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
    Expr(
      :block,
      __source__,
      :($name = $(GlobalRef(Parse, :theory_impl))($parent, $(Expr(:quote, name)), $lines))
    )
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
  mappings = [onlydefault(filter(m -> Name(m[1].head) == j.name, mappings)) for j in dom.judgments]
  composites = map(zip(mappings, dom.judgments)) do (mapping, judgment)
    make_composite(codom, judgment, mapping)
  end
  TheoryMap(dom, codom, composites)
end

function make_composite(
  codom::Theory,
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
  renamed_ctx = Context(map(enumerate(judgment.ctx.ctx)) do (i,nt)
    newname = get(names, Lvl(i; context=true), Anon())
    (newname, nt[2])
  end)
  fc = FullContext(codom.judgments, renamed_ctx)
  if typeof(judgment.head) == TrmCon
    construct_trm(fc, rhs)
  else
    construct_typ(fc, rhs)
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

function term_impl(theory::Theory, expr::Expr0; context = Context())
  construct_trm(FullContext(theory.judgments, context), parse_symexpr(expr))
end

macro term(theory, expr)
  esc(:($(GlobalRef(Parse, :term_impl))($theory, $(Expr(:quote, expr)))))
end

macro term(theory, context, expr)
  esc(:($(GlobalRef(Parse, :term_impl))($theory, $(Expr(:quote, expr)); context=$context)))
end

function context_impl(theory::Theory, expr)
  @match expr begin
    :([$(bindings...)]) => construct_context(theory.judgments, parse_binding.(bindings))
    _ => error("expected a list of bindings")
  end
end

macro context(theory, expr)
  esc(:($(GlobalRef(Parse, :context_impl))($theory, $(Expr(:quote, expr)))))
end

end
