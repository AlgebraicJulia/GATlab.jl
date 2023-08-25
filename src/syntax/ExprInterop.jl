module ExprInterop
export toexpr, fromexpr

using ..Scopes, ..GATs
using ...Util.MetaUtils
using MLStyle 

"""
`toexpr(c::Context, t) -> Any`

Converts Gatlab syntax into an Expr that can be read in via `fromexpr` to get
the same thing. Crucially, the output of this will depend on the order of the
scopes in `c`, and if read back in with a different `c` may end up with
different results.
"""
function toexpr end

"""
`fromexpr(c::Context, e::Any, T::Type) -> Union{T,Nothing}`

Converts a Julia Expr into type T, in a certain scope.
"""
function fromexpr end

function toexpr(c::Context, x::Ident)
  tag_scopelevel = scopelevel(c, gettag(x))
  if isnamed(x)
    if tag_scopelevel == scopelevel(c, nameof(x))
      nameof(x)
    else
      Symbol(nameof(x), "!", tag_scopelevel)
    end
  else
    if tag_scopelevel == length(c)
      Symbol("#", getlevel(x))
    else
      Symbol("#", getlevel(x), "!", tag_scopelevel)
    end
  end
end

const explicit_level_regex = r"^(.*)!(\d+)$"
const unnamed_var_regex = r"^#(\d+)$"

function fromexpr(c::Context, e::Expr0, ::Type{Ident}; sig=nothing)
  e isa Symbol || error("expected a Symbol, got: $e")
  s = string(e)
  m = match(explicit_level_regex, s)
  if !isnothing(m)
    scope = c[parse(Int, m[2])]
    m2 = match(unnamed_var_regex, m[1])
    if !isnothing(m2)
      ident(scope, parse(Int, m2[1]); sig)
    else
      ident(scope, Symbol(m[1]); sig)
    end
  else
    m2 = match(unnamed_var_regex, s)
    if !isnothing(m2)
      ident(c[end], parse(Int, m2[1]); sig)
    else
      ident(c, e; sig)
    end
  end
end

function toexpr(c::Context, ref::Reference)
  if isnothing(rest(ref))
    toexpr(c, first(ref))
  else
    error("paths not supported yet")
  end
end

function fromexpr(c::Context, e, ::Type{Reference}; sig=nothing)
  e isa Symbol || error("paths not supported yet")
  Reference(fromexpr(c, e, Ident; sig))
end

function toexpr(c::Context, term::AlgTerm)
  if term.head isa Constant
    term.head
  else
    if isempty(term.args)
      toexpr(c, term.head)
    else
      Expr(:call, toexpr(c, term.head), toexpr.(Ref(c), term.args)...)
    end
  end
end

function fromexpr(c::Context, e, ::Type{AlgTerm})
  @match e begin
    s::Symbol => begin
      scope = c[scopelevel(c, s)]
      ref = if sigtype(scope) == Union{Nothing, AlgSorts}
        fromexpr(c, s, Reference; sig=AlgSort[])
      else
        fromexpr(c, s, Reference)
      end
      AlgTerm(ref)
    end
    Expr(:call, head, argexprs...) => begin
      args = Vector{AlgTerm}(fromexpr.(Ref(c), argexprs, Ref(AlgTerm)))
      argsorts = AlgSorts(AlgSort.(Ref(c), args))
      AlgTerm(fromexpr(c, head, Reference; sig=argsorts), args)
    end
    e::Expr => error("could not parse AlgTerm from $e")
    x => AlgTerm(Constant(x))
  end
end

function toexpr(c::Context, type::AlgType)
  if isempty(type.args)
    toexpr(c, type.head)
  else
    Expr(:call, toexpr(c, type.head), toexpr.(Ref(c), type.args)...)
  end
end

function fromexpr(c::Context, e, ::Type{AlgType})
  @match e begin
    s::Symbol => AlgType(fromexpr(c, s, Reference))
    Expr(:call, head, args...) =>
      AlgType(fromexpr(c, head, Reference), fromexpr.(Ref(c), args, Ref(AlgTerm)))
    _ => error("could not parse AlgType from $e")
  end
end

function bindingexprs(c::Context, s::Scope)
  c′ = AppendScope(c, s)
  [Expr(:(::), nameof(b), toexpr(c′, getvalue(b))) for b in s]
end

function toexpr(c::Context, binding::JudgmentBinding)
  judgment = getvalue(binding)
  name = nameof(binding)
  c′ = AppendScope(c, judgment.localcontext)
  head = if judgment isa Union{AlgTypeConstructor, AlgTermConstructor}
    if !isempty(judgment.args)
        Expr(:call, name, bindingexprs(c′, judgment.args)...)
    else
        name
    end
  else
    Expr(:call, :(==), toexpr(c′, judgment.equands[1]), toexpr(c′, judgment.equands[2]))
  end
  c″ = judgment isa AlgTermConstructor ? AppendScope(c′, judgment.args) : c′
  headtyped = Expr(:(::), head, judgment isa AlgTypeConstructor ? :TYPE : toexpr(c″, judgment.type))
  if !isempty(judgment.localcontext)
    Expr(:call, :(⊣), headtyped, Expr(:vect, bindingexprs(c, judgment.localcontext)...))
  else
    headtyped
  end
end

"""
@theory ThLawlessCat <: ThGraph begin
  compose(f::Hom(a,b), g::Hom(b,c))::Hom(a,c) ⊣ [a::Ob, b::Ob, c::Ob]
  @op begin
    (⋅) := compose
  end
end
assoc := ((f ⋅ g) ⋅ h) == (f ⋅ (g ⋅ h)) :: Hom(a,d) ⊣ [a::Ob, b::Ob, c::Ob, d::Ob]
otimes(a::Hom(X,Y),b::Hom(P,Q)) ⊣ [(X,Y,P,Q)::Ob]
"""

function fromexpr(c::Context, e, ::Type{Binding{AlgType, Nothing}})
  @match e begin
    Expr(:(::), name::Symbol, type_expr) =>
      Binding{AlgType, Nothing}(name, Set([name]), fromexpr(c, type_expr, AlgType))
    _ => error("could not parse binding of name to type from $e")
  end
end

function parsetypescope(c::Context, exprs::AbstractVector)
  scope = TypeScope()
  c′ = AppendScope(c, scope)
  for expr in exprs
    binding_exprs = @match expr begin
      a::Symbol => [:($a :: default)]
      Expr(:tuple, names...) => [:($name :: default) for name in names]
      Expr(:(::), Expr(:tuple, names...), T) => [:($name :: $T) for name in names]
      :($a :: $T) => [expr]
      _ => error("invalid binding expression $expr")
    end
    for binding_expr in binding_exprs
      binding = fromexpr(c′, binding_expr, Binding{AlgType, Nothing})
      push!(scope, binding)
    end
  end
  scope
end

function normalize_decl(e)
  @match e begin
    :($name := $lhs == $rhs :: $typ ⊣ $ctx) => :((($name := ($lhs == $rhs)) :: $typ) ⊣ $ctx)
    :($lhs == $rhs :: $typ ⊣ $ctx) => :((($lhs == $rhs) :: $typ) ⊣ $ctx)
    :(($lhs == $rhs :: $typ) ⊣ $ctx) => :((($lhs == $rhs) :: $typ) ⊣ $ctx)
    :($lhs == $rhs ⊣ $ctx) => :((($lhs == $rhs) :: default) ⊣ $ctx)
    :($trmcon :: $typ ⊣ $ctx) => :(($trmcon :: $typ) ⊣ $ctx)
    :($trmcon ⊣ $ctx) => :(($trmcon :: default) ⊣ $ctx)
    e => e
  end
end

function parseaxiom(c::Context, localcontext, type_expr, e; name=nothing)
  @match e begin
    Expr(:call, :(==), lhs_expr, rhs_expr) => begin
      equands = fromexpr.(Ref(c), [lhs_expr, rhs_expr], Ref(AlgTerm))
      type = fromexpr(c, type_expr, AlgType)
      axiom = AlgAxiom(localcontext, type, equands)
      JudgmentBinding(name, isnothing(name) ? Set{Symbol}() : Set([name]), axiom)
    end
    _ => error("failed to parse equation from $e")
  end
end

function fromexpr(c::Context, e, ::Type{JudgmentBinding})
  (binding, localcontext) = @match normalize_decl(e) begin
    Expr(:call, :(⊣), binding, Expr(:vect, args...)) => (binding, parsetypescope(c, args))
    e => (e, TypeScope())
  end

  c′ = AppendScope(c, localcontext)
  
  (head, type_expr) = @match binding begin
    Expr(:(::), head, type_expr) => (head, type_expr)
    _ => (binding, :default)
  end

  @match head begin
    Expr(:(:=), name, equation) => parseaxiom(c′, localcontext, type_expr, equation; name)
    Expr(:call, :(==), _, _) => parseaxiom(c′, localcontext, type_expr, head)
    _ => begin
      (name, arglist) = @match head begin
        Expr(:call, name, args...) => (name, args)
        name::Symbol => (name, [])
        _ => error("failed to parse head of term constructor $call")
      end
      args = parsetypescope(c′, arglist)
      @match type_expr begin
        :TYPE => begin
          typecon = AlgTypeConstructor(localcontext, args)
          JudgmentBinding(name, Set([name]), typecon)
        end
        _ => begin
          c″ = AppendScope(c′, args)
          type = fromexpr(c″, type_expr, AlgType)
          termcon = AlgTermConstructor(localcontext, args, type)
          argsorts = map(type -> AlgSort(type.head), getvalue.(args))
          JudgmentBinding(name, Set([name]), termcon, argsorts)
        end
      end
    end
  end
end

function toexpr(c::Context, seg::GATSegment)
  c′ = AppendScope(c, seg)
  e = Expr(:block)
  for binding in seg
    if !isnothing(getline(binding))
      push!(e.args, getline(binding))
    end
    push!(e.args, toexpr(c′, binding))
  end
  e
end

function fromexpr(c::Context, e, ::Type{GATSegment})
  seg = GATSegment()
  e.head == :block || error("expected a block to pars into a GATSegment, got: $e")
  c′ = AppendScope(c, seg)
  linenumber = nothing
  for line in e.args
    @match line begin
      l::LineNumberNode => (linenumber = l)
      Expr(:macrocall, var"@op", _, aliasexpr) => begin
        lines = @match aliasexpr begin
          Expr(:block, lines...) => lines
          _ => [aliasexpr]
        end
        for line in lines
          @match line begin
            _::LineNumberNode => nothing
            :($alias := $name) => addalias!(seg, name, alias)
            _ => error("could not match @op line $line")
          end
        end
      end
      _ => begin
        binding = setline(fromexpr(c′, line, JudgmentBinding), linenumber)
        push!(seg, binding)
      end
    end
  end
  seg
end

end
