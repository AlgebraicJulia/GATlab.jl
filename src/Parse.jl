module Parse
export parse_symexpr, parse_declaration, add_decls, @theory

using ..GATs
using ..GATs: EmptyTheory

using MLStyle
using StructEquality

@struct_hash_equal struct SymExpr
  head::Symbol
  args::Vector{SymExpr}
  function SymExpr(head::Symbol, args::Vector{SymExpr}=SymExpr[])
    new(head, args)
  end
end

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
  context::Vector{Vector{Pair{Symbol, SymExpr}}}
end

const Expr0 = Union{Symbol, Expr}

function parse_args(e::Expr0)
  @match e begin
    (name::Symbol) => (name, Symbol[])
    :($(name::Symbol)($(args...))) => (name, Symbol[args...])
    _ => error("Could not parse $e as an application of a symbol to arguments")
  end
end

function parse_symexpr(e::Expr0)
  @match e begin
    (name::Symbol) => SymExpr(name, SymExpr[])
    Expr(:call, f::Symbol, args...) => SymExpr(f, Vector{SymExpr}(parse_symexpr.(args)))
    _ => error("Could not parse $e as a symbolic expression")
  end
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

function parse_declaration(e::Expr)
  @match e begin
    :($body ⊣ [$(contextexts...)]) =>
      Declaration(
        parse_declbody(body),
        parse_contextext.(contextexts)
      )
    # Expr(:comparison, args...)
    _ => error("Could not parse declaration $e")
  end
end

function parse_contextext(ext::Expr)
  @match ext begin
    :(($(bindings...),)) => parse_binding.(bindings)
    _ => error("could not parse context extension $ext")
  end
end

function parse_binding(binding::Expr)
  @match binding begin
    :($(head::Symbol)::$(type::Expr0)) => (head => parse_symexpr(type))
    _ => error("could not parse binding $binding")
  end
end

function make_context(theory::Context, extension::Vector{Pair{Symbol, SymExpr}})
  Context(theory.depth+1, TheoryExtTerm(
    codom(theory), nullary_termcon.(Ref(theory), extension),
  ))
end

function nullary_termcon(theory::Context, extension::Pair{Symbol, SymExpr})
  TermCon(
    theory,
    extension[1],
    parse_type(codom(theory), extension[2]),
    TermInContext[]
  )
end

function lookup_typecon(::EmptyTheory, name; depth=0)
  error("could not find type constructor $name")
end

function lookup_typecon(theory::TheoryExt, name::Symbol; depth=0)
  index = findfirst(tc -> tc.name == name, theory.typecons)
  if !isnothing(index)
    (depth, index)
  else
    lookup_typecon(parent(theory), name; depth=depth+1)
  end
end

function lookup_termcon(::EmptyTheory, name; depth=0)
  error("could not find term constructor $name")
end

function lookup_termcon(theory::TheoryExt, name::Symbol; depth=0)
  index = findfirst(tc -> tc.name == name, theory.termcons)
  if !isnothing(index)
    (depth, index)
  else
    lookup_termcon(parent(theory), name; depth=depth+1)
  end
end

function parse_term(theory::Theory, e::SymExpr)
  head = lookup_termcon(theory, e.head)
  args = Vector{TermInContext}(parse_term.(Ref(theory), e.args))
  TermInContext(head, args)
end

function parse_type(theory::Theory, e::SymExpr)
  head = lookup_typecon(theory, e.head)
  args = Vector{TermInContext}(parse_term.(Ref(theory), e.args))
  TypeInContext(head, args)
end

function add_decls(theory::Theory, decls::Vector{Declaration}; name=Symbol(""))
  new_typecons = TypeCon[]
  new_termcons = TermCon[]
  new_axioms = Axiom[]
  for decl in decls
    context = foldl(make_context, decl.context; init=Context(0,theory))
    @match decl.body begin
      NewType(head, args) =>
        push!(
          new_typecons,
          TypeCon(
            context,
            head,
            lookup_termcon.(Ref(codom(context)), args)
          )
        )
      NewTerm(head, args, type) =>
        push!(
          new_termcons,
          TermCon(
            context,
            head,
            parse_type(codom(context), type),
            lookup_termcon.(Ref(codom(context)), args)
          )
        )
      NewAxiom(lhs, rhs, type) =>
        push!(
          new_axioms,
          Axiom(
            context,
            Symbol(""),
            parse_type(codom(context), type),
            parse_term(codom(context), lhs),
            parse_term(codom(context), rhs)
          )
        )
    end
  end

  TheoryExt(
    name,
    theory,
    new_typecons,
    new_termcons,
    new_axioms
  )
end

function theory_impl(parent::Theory, lines::Vector)
  foldl((theory, line) -> add_decls(theory, [parse_declaration(line)]), lines; init=parent)
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
      $name = $(GlobalRef(Parse, :theory_impl))($parent, $lines)
    end
  )
end

"""

@theory ThSet <: Empty begin
  Ob::TYPE ⊣ []
end

@theory ThGraph <: ThSet begin
  Hom(x,y)::TYPE ⊣ [(a::Ob, b::Ob)]
end

@theory LawlessCategory <: Graph begin
  compose(f,g)::Hom(a,c) ⊣ [(a::Ob, b::Ob, c::Ob), (f::Hom(a,b), g::Hom(b,c))]
end

"""

end
