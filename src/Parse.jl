module Parse
export parse_symexpr, parse_declaration
using MLStyle

struct SymExpr
    head::Symbol
    args::Vector{SymExpr}
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
        s::Symbol => SymExpr(s,[])
        Expr(:call, f::Symbol, args...) => SymExpr(f, parse_symexpr.(args))
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
        :($(name::Symbol)::$(type::Expr0)) => (name => parse_symexpr(type))
        _ => error("could not parse binding $binding")
    end
end

function extend_theory(theory::Theory, extension::Vector{Pair{Symbol, SymExpr}})
    TheoryExt(
        theory,
        [],
        nullary_term_constructor.(Ref(theory), extension),
        []
    )
end

function nullary_term_constructor(theory::Theory, extension::Pair{Symbol, SymExpr})
    TermConstructor(
        theory,
        extension[1],
        [],
        parse_type(theory, extension[2])
    )
end

function parse_type(theory::Theory, e::SymExpr)
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