# AST
#####

function parse_methodapp(c::GATContext, head::Symbol, argexprs)
  args = Vector{AlgTerm}(fromexpr.(Ref(c), argexprs, Ref(AlgTerm)))
  fun = fromexpr(c, head, Ident)
  signature = AlgSort.(Ref(c), args)
  method = methodlookup(c, fun, signature)
  MethodApp{AlgTerm}(fun, method, args)
end

function fromexpr(c::GATContext, e, ::Type{MethodApp{AlgTerm}})
  @match e begin
    Expr(:call, head::Symbol, argexprs...) => parse_methodapp(c, head, argexprs)
    _ => error("expected a call expression")
  end
end

function toexpr(c::Context, m::MethodApp)
  Expr(:call, toexpr(c, m.head), toexpr.(Ref(c), m.args)...)
end

function fromexpr(c::GATContext, e, ::Type{AlgTerm})
  @match e begin
    s::Symbol => AlgTerm(fromexpr(c, s, Ident))
    Expr(:call, head::Symbol, argexprs...) => AlgTerm(parse_methodapp(c, head, argexprs))
    Expr(:(::), val, type) => Constant(val, fromexpr(c, type, AlgType))
    e::Expr => error("could not parse AlgTerm from $e")
    constant::Constant => AlgTerm(constant)
  end
end

function toexpr(c::Context, term::AlgTerm)
  toexpr(c, term.body)
end

function fromexpr(c::GATContext, e, ::Type{AlgType})::AlgType
  (head, argexprs) = @match e begin
    s::Symbol => (s, [])
    Expr(:call, head, args...) => (head, args)
    _ => error("could not parse AlgType from $e")
  end
  AlgType(parse_methodapp(c, head, argexprs))
end

function toexpr(c::Context, type::AlgType)
  if length(type.body.args) == 0
    toexpr(c, type.body.head)
  else
    Expr(:call, toexpr(c, type.body.head), toexpr.(Ref(c), type.body.args)...)
  end
end

toexpr(c::Context, constant::Constant; kw...) =
  Expr(:(::), constant.value, toexpr(c, constant.type; kw...))

function fromexpr(c::GATContext, e, ::Type{InCtx{T}}; kw...) where T
  (termexpr, localcontext) = @match e begin
    Expr(:call, :(⊣), binding, Expr(:vect, args...)) => (binding, parsetypescope(c, args))
    e => (e, TypeScope())
  end
  term = fromexpr(AppendContext(c, localcontext), termexpr, T)
  InCtx{T}(localcontext, t)
end

function toexpr(c::Context, tic::InCtx; kw...)
  c′ = AppendScope(c, tic.ctx)
  etrm = toexpr(c′, tic.trm; kw...)
  flat = Scopes.flatten(tic.ctx)
  ectx = toexpr(AppendScope(c,flat), flat; kw...)
  Expr(:call, :(⊣), etrm, ectx)
end

# Judgments
###########

# toexpr

function bindingexprs(c::Context, s::HasScope)
  c′ = AppendContext(c, s)
  [Expr(:(::), nameof(b), toexpr(c′, getvalue(b))) for b in s]
end

function toexpr(c::Context, ts::TypeScope)
  Expr(:vect, bindingexprs(c, ts)...)
end

function judgmenthead(_::GAT, name, _::Union{AlgDeclaration, AlgAccessor})
  nothing
end

function judgmenthead(_::GAT, _, judgment::AlgTypeConstructor)
  name = nameof(getdecl(judgment))
  untyped = if isempty(judgment.args)
    name
  else
    Expr(:call, name, nameof.(argsof(judgment))...)
  end
  Expr(:(::), untyped, :TYPE)
end

function judgmenthead(theory::GAT, _, judgment::AlgTermConstructor)
  name = nameof(getdecl(judgment))
  untyped = Expr(:call, name, nameof.(argsof(judgment))...)
  c = GATContext(theory, judgment.localcontext)
  Expr(:(::), untyped, toexpr(c, judgment.type))
end

function judgmenthead(theory::GAT, name, judgment::AlgAxiom)
  c = GATContext(theory, judgment.localcontext)
  untyped = Expr(:call, :(==), toexpr(c, judgment.equands[1]), toexpr(c, judgment.equands[2]))
  Expr(:(::), untyped, toexpr(c, judgment.type))
end

function toexpr(c::GAT, binding::Binding{Judgment})
  judgment = getvalue(binding)
  name = nameof(binding)
  # FIXME
  if judgment isa Alias
    return nothing
  end
  head = judgmenthead(c, name, judgment)
  if isnothing(head)
    return nothing
  end
  Expr(:call, :(⊣), head, Expr(:vect, bindingexprs(c, judgment.localcontext)...))
end

# fromexpr

function fromexpr(c::GATContext, e, ::Type{Binding{AlgType}})
  @match e begin
    Expr(:(::), name::Symbol, type_expr) =>
        Binding{AlgType}(name, fromexpr(c, type_expr, AlgType))
    _ => error("could not parse binding of name to type from $e")
  end
end

function fromexpr(c::GATContext, e, ::Type{TypeScope})
  exprs = e.args
  scope = TypeScope()
  c′ = AppendContext(c, scope)
  line = nothing
  for expr in exprs
    binding_exprs = @match expr begin
      a::Symbol => [Expr(:(::), a, :default)]
      Expr(:tuple, names...) => [:($name :: default) for name in names]
      Expr(:(::), Expr(:tuple, names...), T) => [:($name :: $T) for name in names]
      :($a :: $T) => [expr]
      l::LineNumberNode => begin
        line = l
        []
      end
      _ => error("invalid binding expression $expr")
    end
    for binding_expr in binding_exprs
      binding = fromexpr(c′, binding_expr, Binding{AlgType})
      Scopes.unsafe_pushbinding!(getscope(scope), setline(binding, line))
    end
  end
  scope
end

function parseargs!(theory::GAT, exprs::AbstractVector, scope::TypeScope)
  c = GATContext(theory, scope)
  map(exprs) do expr
    binding_expr = @match expr begin
      a::Symbol => getlid(ident(scope; name=a))
      :($a :: $T) => begin
        binding = fromexpr(c, expr, Binding{AlgType})
        Scopes.unsafe_pushbinding!(scope.scope, binding)
        LID(length(scope))
      end
      _ => error("invalid argument expression $expr")
    end
  end
end

function parseaxiom!(theory::GAT, localcontext, type_expr, e; name=nothing)
  @match e begin
    Expr(:call, :(==), lhs_expr, rhs_expr) => begin
      c = GATContext(theory, localcontext)
      equands = fromexpr.(Ref(c), [lhs_expr, rhs_expr], Ref(AlgTerm))
      type = if isnothing(type_expr)
        infer_type(c, first(equands))
      else
        fromexpr(c, type_expr, AlgType)
      end
      axiom = AlgAxiom(localcontext, type, equands)
      Scopes.unsafe_pushbinding!(theory, Binding{Judgment}(name, axiom))
    end
    _ => error("failed to parse equation from $e")
  end
end

function parseconstructor!(theory::GAT, localcontext, type_expr, e)
  (name, arglist) = @match e begin
    Expr(:call, name, args...) => (name, args)
    name::Symbol => (name, [])
    _ => error("failed to parse head of term constructor $head")
  end
  args = parseargs!(theory, arglist, localcontext)
  @match type_expr begin
    :TYPE => begin
      decl = if hasname(theory, name)
        ident(theory; name)
      else
        Scopes.unsafe_pushbinding!(theory, Binding{Judgment}(name, AlgDeclaration(nothing)))
      end
      typecon = AlgTypeConstructor(decl, localcontext, args)
      X = Scopes.unsafe_pushbinding!(theory, Binding{Judgment}(nothing, typecon))
      for (i, arg) in enumerate(argsof(typecon))
        argname = nameof(arg)
        argdecl = if hasname(theory, argname)
          ident(theory; name=argname)
        else
          Scopes.unsafe_pushbinding!(theory, Binding{Judgment}(argname, AlgDeclaration(nothing)))
        end
        Scopes.unsafe_pushbinding!(theory, Binding{Judgment}(nothing, AlgAccessor(argdecl, decl, X, i)))
      end
    end
    _ => begin
      c = GATContext(theory, localcontext)
      type = fromexpr(c, type_expr, AlgType)
      decl = if hasname(theory, name)
        ident(theory; name)
      else
        Scopes.unsafe_pushbinding!(theory, Binding{Judgment}(name, AlgDeclaration(nothing)))
      end
      termcon = AlgTermConstructor(decl, localcontext, args, type)
      Scopes.unsafe_pushbinding!(theory, Binding{Judgment}(nothing, termcon))
    end
  end
end

"""
This is necessary because the intuitive precedence rules for the symbols
that we use do not match the Julia precedence rules. In theory, this could
be written with some algorithm that recalculates precedence, but I am too lazy
to write that, so instead I just special case everything.
"""
function normalize_judgment(e)
  @match e begin
    :($name := $lhs == $rhs :: $typ ⊣ $ctx) => :((($name := ($lhs == $rhs)) :: $typ) ⊣ $ctx)
    :($lhs == $rhs :: $typ ⊣ $ctx) => :((($lhs == $rhs) :: $typ) ⊣ $ctx)
    :(($lhs == $rhs :: $typ) ⊣ $ctx) => :((($lhs == $rhs) :: $typ) ⊣ $ctx)
    :($trmcon :: $typ ⊣ $ctx) => :(($trmcon :: $typ) ⊣ $ctx)
    :($name := $lhs == $rhs ⊣ $ctx) => :((($name := ($lhs == $rhs))) ⊣ $ctx)
    :($lhs == $rhs ⊣ $ctx) => :(($lhs == $rhs) ⊣ $ctx)
    :($(trmcon::Symbol) ⊣ $ctx) => :(($trmcon :: default) ⊣ $ctx)
    :($f($(args...)) ⊣ $ctx) && if f ∉ [:(==), :(⊣)] end => :(($f($(args...)) :: default) ⊣ $ctx)
    trmcon::Symbol => :($trmcon :: default)
    :($f($(args...))) && if f ∉ [:(==), :(⊣)] end => :($e :: default)
    _ => e
  end
end

function parse_binding_line!(theory::GAT, e, linenumber)
  e = normalize_judgment(e)

  (binding, localcontext) = @match e begin
    Expr(:call, :(⊣), binding, ctxexpr) && if ctxexpr.head == :vect end =>
      (binding, fromexpr(GATContext(theory), ctxexpr, TypeScope))
    e => (e, TypeScope())
  end

  c = GATContext(theory, localcontext)

  (head, type_expr) = @match binding begin
    Expr(:(::), head, type_expr) => (head, type_expr)
    _ => (binding, nothing)
  end

  @match head begin
    Expr(:(:=), name, equation) => parseaxiom!(theory, localcontext, type_expr, equation; name)
    Expr(:call, :(==), _, _) => parseaxiom!(theory, localcontext, type_expr, head)
    _ => parseconstructor!(theory, localcontext, type_expr, head)
  end
end

# GATs
######

"""
This only works when `seg` is a segment of `theory`
"""
function toexpr(theory::GAT, seg::GATSegment)
  e = Expr(:block)
  for binding in seg
    if !isnothing(getline(binding))
      push!(e.args, getline(binding))
    end
    line = toexpr(theory, binding)
    if !isnothing(line)
      push!(e.args, line)
    end
  end
  e
end

function parse_gat_line!(theory::GAT, e::Expr, linenumber)
  @match e begin
    Expr(:macrocall, var"@op", _, aliasexpr) => begin
      lines = @match aliasexpr begin
        Expr(:block, lines...) => lines
        _ => [aliasexpr]
      end
      for line in lines
        @switch line begin
          @case (_::LineNumberNode)
            nothing
          @case :($alias := $name)
            # check if there is already a declaration for name, if not, create declaration
            decl = if hasname(theory, name)
              ident(theory; name)
            else
              Scopes.unsafe_pushbinding!(theory, Binding{Judgment}(name, AlgDeclaration(nothing)))
            end
            binding = Binding{Judgment}(alias, Alias(decl), linenumber)
            Scopes.unsafe_pushbinding!(theory, binding)
          @case _
            error("could not match @op expression $line")
        end
      end
    end
    Expr(:import, Expr(:(:), Expr(:(.), mod), imports)) => begin
      # create appropriate declarations
    end
    _ => begin
      parse_binding_line!(theory, e, linenumber)
    end
  end
end

function fromexpr(parent::GAT, e, ::Type{GAT}; name=parent.name)
  theory = copy(parent; name)
  unsafe_newsegment!(theory)
  e.head == :block || error("expected a block to parse into a GAT, got: $e")
  linenumber = nothing
  for line in e.args
    bindings = @match line begin
      l::LineNumberNode => begin
        linenumber = l
      end
      _ => parse_gat_line!(theory, line, linenumber)
    end
  end
  theory
end