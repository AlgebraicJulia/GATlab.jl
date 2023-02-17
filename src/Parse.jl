module Parse
export parse_symexpr, parse_declaration, add_decls

using ..GATs

using MLStyle
using StructEquality

@struct_hash_equal struct SymExpr
  head::Symbol
  args::Vector{SymExpr}
  function SymExpr(head::Symbol, args::Vector{SymExpr}=SymExpr[])
    new(head, args)
  end
end

struct Declaration
  head::Symbol
  args::Vector{Symbol}
  type::SymExpr
  context::Vector{Vector{Pair{Symbol, SymExpr}}}
end

const Expr0 = Union{Symbol, Expr}

function parse_symexpr(e::Expr0)
  @match e begin
    s::Symbol => SymExpr(s,SymExpr[])
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

function parse_declaration(e::Expr)
  @match e begin
    :($(head::Symbol)($(args...))::$type ⊣ [$(contextexts...)]) =>
      Declaration(
        head,
        args,
        parse_symexpr(type),
        parse_contextext.(contextexts)
      )
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

function extend_theory(theory::Theory, extension::Vector{Pair{Symbol, SymExpr}})
  TheoryExt(
    Symbol(""),
    theory,
    TypeInContext[],
    nullary_termcon.(Ref(theory), extension),
    Axiom[]
  )
end

function nullary_termcon(theory::Theory, extension::Pair{Symbol, SymExpr})
  TermCon(
    theory,
    extension[1],
    parse_type(theory, extension[2]),
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
  new_typecons = map(filter(decl -> decl.type == SymExpr(:TYPE), decls)) do decl
    context = foldl(extend_theory, decl.context; init=theory)
    TypeCon(
      context,
      decl.head,
      lookup_termcon.(Ref(context), decl.args)
    )
  end
  new_termcons = map(filter(decl -> decl.type != SymExpr(:TYPE), decls)) do decl
    context = foldl(extend_theory, decl.context; init=theory)
    TermCon(
      context,
      decl.head,
      parse_type(context, decl.type),
      lookup_termcon.(Ref(context), decl.args)
    )
  end
  TheoryExt(
    name,
    theory,
    new_typecons,
    new_termcons,
    Axiom[]
  )
end

"""

@theory Set <: Empty begin
  Ob::TYPE ⊣ []
end

@theory Graph <: Set begin
  Hom(x,y)::TYPE ⊣ [(a::Ob, b::Ob)]
end

@theory LawlessCategory <: Graph begin
  compose(f,g)::Hom(a,c) ⊣ [(a::Ob, b::Ob, c::Ob), (f::Hom(a,b), g::Hom(b,c))]
end

"""

end
