module TheoryMacros
export @theory, @theorymap, @term, @aterm, @context

using MLStyle

using ...Syntax
using ...Util
using ...Models.AugmentedTheories

using ..Parsing

function construct_typ(fc::FullContext, e::CallExpr)
  head = lookup(fc, e.head)
  Typ(head, construct_trm.(Ref(fc), e.args))
end

construct_trm(::FullContext, t::InjectedTrm) = t.trm

function construct_trm(fc::FullContext, e::CallExpr)
  args = construct_trm.(Ref(fc), e.args)
  argsorts = Vector{Lvl}(getsort.(Ref(fc), args))
  head = lookup(fc, SortSignature(e.head, argsorts))
  Trm(head, args)
end

function construct_atyp(fc::FullContext, e::CallExpr; interp_val=(_ -> nothing))
  head = lookup(fc, e.head)
  ATyp(head, map(arg -> construct_atrm(fc, arg; interp_val), e.args))
end

function construct_atrm(fc::FullContext, e::CallExpr; interp_val=(_ -> nothing))
  head = lookup(fc, e.head)
  ATrmCon(head, map(arg -> construct_atrm(fc, arg; interp_val), e.args))
end

construct_atrm(::FullContext, t::InjectedTrm; interp_val=(_ -> nothing)) = ATrm(t.trm)

function construct_atrm(::FullContext, v::RawVal; interp_val=(_ -> nothing))
  atrm = interp_val(v.val)
  !isnothing(atrm) || error("could not construct constant from $(v.val)")
  atrm
end

function construct_context(t::Theory, symctx::Vector{Pair{Name, SurfaceExpr}})
  c = Context()
  fc = FullContext(t, c)
  for (n, symtyp) in symctx
    push!(c.ctx, (n, construct_typ(fc, symtyp)))
  end
  c
end

function construct_context(t::Theory, ctxexpr::Expr)
  @match ctxexpr begin
    :([$(bindings...)]) => construct_context(t, parse_bindings(bindings))
    _ => error("expected a context of the form [bindings...], got: $ctxexpr")
  end
end

function construct_judgment(t::Theory, decl::Declaration)
  context = construct_context(t, decl.context)
  fc = FullContext(t, context)
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
  t = Theory(Name(name), copy(precursor.judgments), copy(precursor.aliases))
  for line in lines
    @match line begin
      Expr(:macrocall, &(Symbol("@op")), _, aliasblock) => begin
        aliases = @match aliasblock begin
          Expr(:block, lines...) => lines
          _ => [aliasblock]
        end
        for alias in aliases
          @match alias begin
            Expr(:(:=), newname, oldname) => begin
              i = lookup(t, oldname)
              t.aliases[SortSignature(Name(newname), SortSignature(t.judgments[index(i)]).sorts)] = i
            end
            _ => nothing
          end
        end
      end
      _ => begin
        j = construct_judgment(t, parse_decl(line))
        push!(t.judgments, j)
        if j.head isa Constructor
          t.aliases[SortSignature(j)] = Lvl(length(t.judgments))
        end
      end
    end
  end
  t
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
  parent::Theory,
  usings::Vector{Tuple{Theory, Dict{Name,Name}}}
)
  cur = parent
  incl = collect(1:length(parent.judgments))
  for (t, renamings) in usings
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

function import_tags(name::Expr0, parent::Theory)
  tagnames = [Symbol(j.name) for j in parent.judgments if j.head isa Constructor && j.name isa SymLit]
  Expr(:using, Expr(:(:), Expr(:(.), :(.), :(.), name), Expr.(Ref(:(.)), tagnames)...))
end

macro theory(head, body)
  (name, parent_module) = @match head begin
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
  parent = macroexpand(__module__, :($parent_module.@theory()))
  usings = Tuple{Theory, Dict{Name, Name}}[
    (macroexpand(__module__, :($T.@theory)), renames)
    for (T, renames) in usings
  ]
  precursor = theory_precursor(parent, usings)
  theory = theory_impl(precursor, name, judgments)
  typ_cons = [
    (j.name.name, :(struct $(j.name.name) <: $(GlobalRef(Theories, :TypTag)){$i} end))
    for (i,j) in enumerate(theory.judgments[(length(parent.judgments)+1):end])
      if (typeof(j.head) == TypCon) && (typeof(j.name) == SymLit)
  ]
  trm_cons = [
    (j.name.name, :(struct $(j.name.name) <: $(GlobalRef(Theories, :TrmTag)){$i} end))
    for (i,j) in enumerate(theory.judgments[(length(parent.judgments)+1):end])
      if (typeof(j.head) == TrmCon) && (typeof(j.name) == SymLit)
  ]
  exports = [first.(typ_cons); first.(trm_cons)]
  esc(Expr(:toplevel, :(
    module $name
    export $(exports...)
    $(import_tags(parent_module, parent))
    $(last.(typ_cons)...)
    $(last.(trm_cons)...)
    struct T <: $(GlobalRef(Theories, :AbstractTheory)) end
    macro theory()
      $theory
    end
    $(GlobalRef(Theories, :gettheory))(::T) = $theory
    end
  )))
end

function parse_mapping(expr)
  @match expr begin
    :($lhs => $rhs) => (parse_surface(lhs) => parse_surface(rhs))
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
  composites = Composite[]
  f = TheoryMap(dom, codom, composites; partial=true)
  for (mapping, judgment) in zip(mappings, dom.judgments)
    push!(composites, make_composite(codom, judgment, mapping, f))
  end
  f
end

theorymap_impl(dom::Type{<:AbstractTheory}, codom::Type{<:AbstractTheory}, lines::Vector) =
    theorymap_impl(gettheory(dom), gettheory(codom), lines)

function make_composite(
  codom::Theory,
  judgment::Judgment,
  mapping::Union{Pair{CallExpr, CallExpr}, Nothing},
  f::TheoryMap
)
  if isnothing(mapping)
    typeof(judgment.head) == Axiom || error("must provide a mapping for $(judgment.name)")
    return nothing
  end
  lhs, rhs = mapping
  all(length(arg.args) == 0 for arg in lhs.args) || error("left side of mapping must be a flat expression")
  length(lhs.args) == arity(judgment.head) || error("wrong number of arguments for $(judgment.name)")
  names = Dict(zip(judgment.head.args, Name.(gethead.(lhs.args))))
  renamed_ctx = Context(map(enumerate(judgment.ctx.ctx)) do (i,nt)
    newname = get(names, Lvl(i; context=true), Anon())
    (newname, f(nt[2]))
  end)
  fc = FullContext(codom, renamed_ctx)
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
      $(GlobalRef(TheoryMacros, :theorymap_impl))($dom.T, $codom.T, $lines)
    end
  )
end

function term_impl(theory::Theory, expr::Union{Trm,Expr0}; context = Context())
  construct_trm(FullContext(theory, context), parse_surface(expr))
end

function aterm_impl(theory::Theory, interp_val, expr::Union{Trm,Expr0}; context = Context())
  construct_atrm(FullContext(theory, context), parse_surface(expr); interp_val)
end

term_impl(theory::Type{<:AbstractTheory}, expr::Expr0; context = Context()) =
  term_impl(gettheory(theory), expr; context)

term_impl(theory::Type{AT}, expr::Expr0; context = Context()) where {T, AT<:AugmentedTheory{T}} =
  aterm_impl(gettheory(T), x -> interp_val(AT(), x), expr; context)

term_impl(theory::Module, expr::Expr0; context=Context()) = term_impl(theory.T, expr; context)

macro term(theory, expr)
  esc(:($(GlobalRef(TheoryMacros, :term_impl))($theory, $(Expr(:quote, expr)))))
end

macro term(theory, context, expr)
  esc(:($(GlobalRef(TheoryMacros, :term_impl))($theory, $(Expr(:quote, expr)); context=$context)))
end

function context_impl(T::Type{<:AbstractTheory}, expr)
  T = gettheory(T)
  @match expr begin
    :([$(bindings...)]) => construct_context(T, parse_bindings(bindings))
    _ => error("expected a list of bindings")
  end
end

macro context(theory, expr)
  esc(:($(GlobalRef(TheoryMacros, :context_impl))($theory.T, $(Expr(:quote, expr)))))
end


end
