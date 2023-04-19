module TheoryMacros
export @theory, @theorymap, @term, @context

using MLStyle

using ...Models
using ...Syntax
using ...Util

using ..Parsing

function construct_typ(fc::FullContext, e::SymExpr)
  head = lookup(fc, e.head)
  Typ(head, construct_trm.(Ref(fc), e.args))
end

function construct_trm(fc::FullContext, e::SymExpr)
  head = lookup(fc, e.head)
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

function construct_context(judgments::Vector{Judgment}, ctxexpr::Expr)
  @match ctxexpr begin
    :([$(bindings...)]) => construct_context(judgments, parse_bindings(bindings))
    _ => error("expected a context of the form [bindings...], got: $ctxexpr")
  end
end

function construct_judgment(judgments::Vector{Judgment}, decl::Declaration)
  context = construct_context(judgments, decl.context)
  fc = FullContext(judgments, context)
  (name, head) = @match decl.body begin
    NewTerm(head, args, type) =>
      (
        head,
        TrmCon(lookup.(Ref(fc), args), construct_typ(fc, type))
      )
    NewType(head, args) =>
      (
        head,
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

function theory_impl(precursor::Theory, name::Symbol, lines::Vector)
  judgments = copy(precursor.judgments)
  for line in lines
    push!(judgments, construct_judgment(judgments, parse_decl(line)))
  end
  Theory(Name(name), judgments)
end

theory_impl(precursor::Type{<:AbstractTheory}, name::Symbol, lines::Vector) =
  theory_impl(gettheory(precursor), name, lines)

function rename_by(t::Theory, renamings::Dict{Name,Name})
  by_int = Dict{Int,Name}()
  for (i,j) in enumerate(t.judgments)
    if j.name ∈ keys(renamings)
      by_int[i] = renamings[j.name]
    end
  end
  by_int
end

function theory_precursor(
  parent::Type{<:AbstractTheory},
  usings::Vector{Tuple{DataType, Dict{Name,Name}}}
)
  parent = gettheory(parent)
  cur = parent
  incl = collect(1:length(parent.judgments))
  for (T, renamings) in usings
    t = gettheory(T)
    cur = pushout(
      Anon(),
      TheoryIncl(parent, cur, incl),
      TheoryIncl(parent, t, incl);
      rename_c=rename_by(t, renamings)
    )[1]
  end
  cur
end

function parse_rename(rename::Expr)
  @match rename begin
    Expr(:as, Expr(:., lhs), rhs) => (Name(lhs) => Name(rhs))
    _ => error("invalid renaming syntax")
  end
end

macro theory(head, body)
  (name, parent) = @match head begin
    :($(name::Symbol) <: $(parent::Symbol)) => (name, parent)
    _ => error("expected head of @theory macro to be in the form name <: parent")
  end
  lines = @match body begin
    Expr(:block, lines...) => lines
    _ => error("expected body of @theory macro to be a block")
  end
  judgments = Expr[]
  usings = Tuple{Expr0, Dict{Name,Name}}[]
  for line in lines
    @match line begin
      (::LineNumberNode) => nothing
      Expr(:using, Expr(:., T)) => push!(usings, (T, Dict{Name,Name}()))
      Expr(:using, Expr(:(:), Expr(:., T), renames...)) =>
        push!(usings, (T, Dict{Name,Name}(parse_rename.(renames))))
      l => push!(judgments, l)
    end
  end
  # we use :ref instead of :vect so that we construct a vector of the proper
  # type when there are no using statements
  usings = Expr(
    :ref,
    Tuple{DataType, Dict{Name,Name}},
    [Expr(:tuple, T, renames) for (T, renames) in usings]...
  )
  precursor = gensym(:precursor)
  tmp = gensym(:theory)
  esc(
    Expr(
      :block,
      :(const $precursor = $(GlobalRef(TheoryMacros, :theory_precursor))(
        $parent,
        $usings
      )),
      :(const $tmp = $(GlobalRef(TheoryMacros, :theory_impl))(
         $precursor,
         $(Expr(:quote, name)),
         $judgments
      )),
      __source__,
      :(struct $name <: $(GlobalRef(Theories, :AbstractTheory)) end),
      :($(GlobalRef(Theories, :gettheory))(::$name) = $tmp)
    )
  )
end

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

theorymap_impl(dom::Type{<:AbstractTheory}, codom::Type{<:AbstractTheory}, lines::Vector) =
    theorymap_impl(gettheory(dom), gettheory(codom), lines)

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
  lines = getlines(body)
  esc(
    quote
      $(GlobalRef(TheoryMacros, :theorymap_impl))($dom, $codom, $lines)
    end
  )
end

function term_impl(theory::Theory, expr::Expr0; context = Context())
  construct_trm(FullContext(theory.judgments, context), parse_symexpr(expr))
end

term_impl(intheory::Type{<:AbstractTheory}, expr::Expr0; context = Context()) =
  term_impl(gettheory(intheory), expr; context)

macro term(theory, expr)
  esc(:($(GlobalRef(TheoryMacros, :term_impl))($theory, $(Expr(:quote, expr)))))
end

macro term(theory, context, expr)
  esc(:($(GlobalRef(TheoryMacros, :term_impl))($theory, $(Expr(:quote, expr)); context=$context)))
end

function context_impl(T::Type{<:AbstractTheory}, expr)
  T = gettheory(T)
  @match expr begin
    :([$(bindings...)]) => construct_context(T.judgments, parse_bindings(bindings))
    _ => error("expected a list of bindings")
  end
end

macro context(theory, expr)
  esc(:($(GlobalRef(TheoryMacros, :context_impl))($theory, $(Expr(:quote, expr)))))
end


end
