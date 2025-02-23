# AST
#####
"""Coerce GATs to GAT contexts"""
fromexpr(g::GAT, e, t) = fromexpr(GATContext(g), e, t)

function parse_methodapp(c::GATContext, head::Symbol, argexprs)
  args = Vector{AlgTerm}(fromexpr.(Ref(c), argexprs, Ref(AlgTerm)))
  fun = fromexpr(c, head, Ident)
  signature = AlgSort.(Ref(c), args)
  method = try
    methodlookup(c, fun, signature)
  catch e
    error("couldn't find method for $(Expr(:call, head, argexprs...))")
  end
  MethodApp{AlgTerm}(fun, method, args)
end

function toexpr(c::Context, m::MethodApp)
  Expr(:call, toexpr(c, m.head), toexpr.(Ref(c), m.args)...)
end

function toexpr(c::Context, m::AlgDot)
  Expr(:.,  toexpr(c, m.body), QuoteNode(m.head))
end

function fromexpr(c::GATContext, e, ::Type{AlgTerm})
  @match e begin
    s::Symbol => begin
      x = fromexpr(c, s, Ident)
      value = getvalue(c[x])
      if value isa AlgType
        AlgTerm(fromexpr(c, s, Ident))
      else
        error("nullary constructors must be explicitly called: $e")
      end
    end
    Expr(:., body, QuoteNode(head)) => begin 
      t = fromexpr(c, body, AlgTerm)
      algstruct = c[AlgSort(c, t).method] |> getvalue
      AlgTerm(AlgDot(ident(algstruct.fields; name=head), t))# , str))
  end
    Expr(:call, head::Symbol, argexprs...) => AlgTerm(parse_methodapp(c, head, argexprs))
    Expr(:(::), val, type) => AlgTerm(Constant(val, fromexpr(c, type, AlgType)))
    e::Expr => error("could not parse AlgTerm from $e")
    constant::Constant => AlgTerm(constant)
  end
end

function toexpr(c::Context, term::AlgTerm)
  toexpr(c, term.body)
end

function fromexpr(p::GATContext, e, ::Type{AlgType})::AlgType
  @match e begin
    s::Symbol => AlgType(parse_methodapp(p, s, []))
    Expr(:call, head, args...) && if head != :(==) end =>
      AlgType(parse_methodapp(p, head, args))
    Expr(:call, :(==), lhs, rhs) =>
      AlgType(p, fromexpr(p, lhs, AlgTerm), fromexpr(p, rhs, AlgTerm))
    _ => error("could not parse AlgType from $e")
  end
end

function toexpr(c::Context, type::AlgType)
  if isapp(type)
    if length(type.body.args) == 0
      toexpr(c, type.body.head)
    else
      Expr(:call, toexpr(c, type.body.head), toexpr.(Ref(c), type.body.args)...)
    end
  elseif iseq(type)
    Expr(:call, :(==), toexpr.(Ref(c), type.body.equands)...)
  end
end

function fromexpr(c::GATContext, e, ::Type{AlgSort})
  e isa Symbol || error("expected a Symbol to parse a sort, got: $e")
  decl = ident(c.theory; name=e)
  method = only(allmethods(c.theory.resolvers[decl]))[2]
  AlgSort(decl, method)
end

function toexpr(c::GATContext, s::AlgSort)
  toexpr(c, getdecl(s))
end

toexpr(c::Context, constant::Constant; kw...) =
  Expr(:(::), constant.value, toexpr(c, constant.type; kw...))

function fromexpr(c::GATContext, e, ::Type{InCtx{T}}; kw...) where T
  (termexpr, localcontext) = @match e begin
    Expr(:call, :(⊣), binding, tscope) => (binding, fromexpr(c, tscope, TypeScope))
    e => (e, TypeScope())
  end
  term = fromexpr(AppendContext(c, localcontext), termexpr, T)
  InCtx{T}(localcontext, term)
end

function toexpr(c::Context, tic::InCtx; kw...)
  c′ = AppendContext(c, tic.ctx)
  etrm = toexpr(c′, tic.val; kw...)
  flat = TypeScope(tic.ctx)
  ectx = toexpr(c, flat; kw...)
  Expr(:call, :(⊣), etrm, ectx)
end

# Judgments
###########

function toexpr(p::Context, b::Binding{AlgType})
  Expr(:(::), nameof(b), toexpr(p, getvalue(b)))
end

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
  if isnothing(name)
    untyped
  else 
    Expr(:(:=), name, untyped)
  end
end

function judgmenthead(theory::GAT, name′, judgment::AlgFunction)
  isnothing(name′) || error("AlgFunction received name argument $name′")
  name = nameof(getdecl(judgment))
  call = Expr(:call, name, nameof.(argsof(judgment))...)
  val = toexpr(GATContext(theory, judgment.localcontext), judgment.value)
  Expr(:(:=), call, val)
end

function toexpr(theory::GAT, judgment::AlgStruct)
  name = nameof(getdecl(judgment))
  ctx = GATContext(theory, judgment.localcontext)
  callargs = [toexpr(ctx, a) for a in typeargsof(judgment)]
  body = [toexpr(ctx, a) for a in argsof(judgment)]
  call = Expr(:call, name, callargs...)
  lc = [b for (i,b) in enumerate(getbindings(judgment.localcontext)) 
        if LID(i) ∉ judgment.typeargs ∪ judgment.fields] |> TypeScope
  stexpr = Expr(:struct, false, call, Expr(:block, body...))
  if isempty(lc) 
    return stexpr 
  else 
    return Expr(:call, :⊣, stexpr, toexpr(theory, lc))
  end
end



function toexpr(c::GAT, binding::Binding{Judgment})
  judgment = getvalue(binding)
  name = nameof(binding)
  # FIXME
  if judgment isa Alias
    return nothing
  elseif judgment isa AlgStruct 
    return toexpr(c, judgment)
  end
  head = judgmenthead(c, name, judgment)
  if isnothing(head)
    return nothing
  end
  Expr(:call, :(⊣), head, Expr(:vect, bindingexprs(c, judgment.localcontext)...))
end

# fromexpr

"""
`f(pushbinding!, expr)` should inspect `expr` and call `pushbinding!`
0 or more times with two arguments: the name and value of a new binding.
"""
function parse_scope!(f::Function, scope::Scope, lines::AbstractVector)
  currentln = nothing
  for e in lines
    @match e begin
      l::LineNumberNode => (currentln = l)
      _ => f(e) do binding
        # @info "CURRENT LINE!!!" currentln
        # @info "IS BEING SET!!!" setline(binding, currentln) isnothing(currentln)
        Scopes.unsafe_pushbinding!(scope, setline(binding, currentln))
      end
    end
  end
  scope
end

function fromexpr(c::GATContext, e, ::Type{Binding{AlgType}}; line=nothing)
  @match e begin
    Expr(:(::), name::Symbol, type_expr) =>
        Binding{AlgType}(name, fromexpr(c, type_expr, AlgType), line)
    _ => error("could not parse binding of name to type from $e")
  end
end

function parse_binding_expr!(c::GATContext, pushbinding!, e)
  p!(name, type_expr) = pushbinding!(Binding{AlgType}(name, fromexpr(c, type_expr, AlgType)))
  @match e begin
    a::Symbol => p!(a, :default)
    Expr(:tuple, names...) => p!.(names, Ref(:default))
    Expr(:(::), Expr(:tuple, names...), T) => p!.(names, Ref(T))
    Expr(:(::), name, T) => p!(name, T)
    Expr(:call, :(==), lhs, rhs) =>
      pushbinding!(Binding{AlgType}(
        nothing, AlgType(c, fromexpr(c, lhs, AlgTerm), fromexpr(c, rhs, AlgTerm))
      ))
    _ => error("invalid binding expression $e")
  end
end

function fromexpr(p::GATContext, e, ::Type{TypeScope})
  ts = TypeScope()
  c = AppendContext(p, ts)
  parse_scope!(ts.scope, e.args) do pushbinding!, arg
    parse_binding_expr!(c, pushbinding!, arg)
  end
  ts
end

function parseargs!(theory::GAT, exprs::AbstractVector, scope::TypeScope)
  c = GATContext(theory, scope)
  linenumber = nothing
  Vector{LID}(filter(x->x isa LID, map(exprs) do expr
    binding_expr = @match expr begin
      a::Symbol => getlid(ident(scope; name=a))
      l::LineNumberNode => begin linenumber = l end
      :($a :: $T) => begin
        binding = fromexpr(c, expr, Binding{AlgType})
        Scopes.unsafe_pushbinding!(scope.scope, setline(binding, linenumber))
        LID(length(scope))
      end
      _ => error("invalid argument expression $expr")
    end
  end))
end

function parseaxiom!(theory::GAT, localcontext, sort_expr, e; name=nothing)
  @match e begin
    Expr(:call, :(==), lhs_expr, rhs_expr) => begin
      c = GATContext(theory, localcontext)
      equands = fromexpr.(Ref(c), [lhs_expr, rhs_expr], Ref(AlgTerm))
      sorts = sortcheck.(Ref(c), equands)
      @assert allequal(sorts)
      sort = if isnothing(sort_expr)
        first(sorts)
      else
        fromexpr(c, sort_expr, AlgSort)
      end
      axiom = AlgAxiom(localcontext, sort, equands)
      Scopes.unsafe_pushbinding!(theory, Binding{Judgment}(name, axiom))
    end
    _ => error("failed to parse equation from $e")
  end
end

function parseconstructor!(theory::GAT, localcontext, type_expr, e)
  (name, arglist) = @match e begin
    Expr(:call, name, args...) => (name, args)
    name::Symbol => (name, [])
    _ => error("failed to parse head of term constructor $e")
  end
  args = parseargs!(theory, arglist, localcontext)
  @match type_expr begin
    Expr(:curly, :TYPE, Ty) => begin 
      new_typecon(theory, name, localcontext, args)
      res = last(only(values(theory.resolvers[ident(theory; name)])))      
      theory.fixed_types[AlgSort(getdecl(getvalue(theory[res])), res)] = Ty
    end
    :TYPE => new_typecon(theory, name, localcontext, args)
    _ => begin
      c = GATContext(theory, localcontext)
      type = @match type_expr begin 
        Expr(:vect, _...) => fromexpr(c, type_expr, TypeScope)
        _ => fromexpr(c, type_expr, AlgType)
      end      
      decl = hasname!(theory, name)
      termcon = AlgTermConstructor(decl, localcontext, args, type)
      m = Scopes.unsafe_pushbinding!(theory, Binding{Judgment}(nothing, termcon))
    end
  end
end

function new_typecon(theory, name, localcontext, args)
  decl = hasname!(theory, name)
  typecon = AlgTypeConstructor(decl, localcontext, args)
  X = Scopes.unsafe_pushbinding!(theory, Binding{Judgment}(nothing, typecon))
  for (i, arg) in enumerate(argsof(typecon))
    argname = nameof(arg)
    argdecl = hasname!(theory, argname)
    Scopes.unsafe_pushbinding!(theory, Binding{Judgment}(nothing, AlgAccessor(argdecl, decl, X, i)))
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
    :($name := $fun ⊣ $ctx) => :(($name := $fun) ⊣ $ctx)
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
      (binding, fromexpr(theory, ctxexpr, TypeScope))
    e => (e, TypeScope())
  end

  c = GATContext(theory, localcontext)

  (head, type_expr) = @match binding begin
    Expr(:(::), head, type_expr) => (head, type_expr)
    _ => (binding, nothing)
  end

  @match head begin
    Expr(:(:=), name, equation) => @match equation begin 
      Expr(:call, :(==), _, _) => parseaxiom!(theory, localcontext, type_expr, equation; name)
      _ => parsefunction!(theory, localcontext, type_expr, name, equation)
    end
    Expr(:call, :(==), _, _) => parseaxiom!(theory, localcontext, type_expr, head)
    _ => parseconstructor!(theory, localcontext, type_expr, head)
  end
end

function  parsefunction!(theory::GAT, localcontext, sort_expr, call, e)
  isnothing(sort_expr) || error("No explicit sort for functions $call :: $sort_expr")
  name, args′ = @match call begin
    Expr(:call, name, args...) => (name, args)
  end
  args = parseargs!(theory, args′, localcontext)
  c = GATContext(theory, localcontext)
  decl = hasname!(theory, name)
  trm = fromexpr(c, e, AlgTerm)
  fun = AlgFunction(decl, localcontext, args, trm)
  Scopes.unsafe_pushbinding!(theory, Binding{Judgment}(nothing, fun))
end

function parse_struct!(theory::GAT, e, linenumber, ctx=nothing)
  localcontext = isnothing(ctx) ? TypeScope() : fromexpr(theory, ctx, TypeScope)
  (name, args...) = @match e begin 
    Expr(:struct, false, Expr(:call, name, lc...), Expr(:block, body...)) => begin
      typeargs = parseargs!(theory, lc, localcontext)
      args = fromexpr(GATContext(theory, localcontext),Expr(:vect,body...),TypeScope)  
      (name, localcontext, typeargs, args)
    end
  end
  decl = hasname!(theory, name)
  str = AlgStruct(decl, args...)
  X = Scopes.unsafe_pushbinding!(theory, Binding{Judgment}(nothing, str))

  for arg in typeargsof(str)
    argname = nameof(arg)
    i = ident(localcontext; name=argname).lid.val
    argdecl = hasname!(theory, argname)
    b = Binding{Judgment}(nothing, AlgAccessor(argdecl, decl, X, i))
    Scopes.unsafe_pushbinding!(theory, b)
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

function parse_gat_line!(theory::GAT, e::Expr, linenumber; current_module)
  try
    @match e begin
      Expr(:struct, _...) => parse_struct!(theory, e, linenumber)
      Expr(:call, :⊣, Expr(:struct, _...), ctx) => parse_struct!(theory, e.args[2], linenumber, ctx)
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
              decl = hasname!(theory, name)
              binding = Binding{Judgment}(alias, Alias(decl), linenumber)
              Scopes.unsafe_pushbinding!(theory, binding)
            @case _
              error("could not match @op expression $line")
          end
        end
      end
      # already handled earlier
      Expr(:using, _) => nothing
      _ => begin
        parse_binding_line!(theory, e, linenumber)
      end
    end
  catch _
    error("error parsing expression $e at line $linenumber")
  end
end

function fromexpr(parent::GAT, e, ::Type{GAT}; name=parent.name, current_module::Vector{Symbol}=Symbol[])
  theory = copy(parent; name)
  unsafe_newsegment!(theory)
  e.head == :block || error("expected a block to parse into a GAT, got: $e")
  linenumber = nothing
  for line in e.args
    @match line begin
      l::LineNumberNode => begin
        linenumber = l
      end
      _ => parse_gat_line!(theory, line, linenumber; current_module)
    end
  end
  theory
end
