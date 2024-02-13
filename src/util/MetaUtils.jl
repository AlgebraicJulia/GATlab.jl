""" General-purpose tools for metaprogramming in Julia.
"""
module MetaUtils
export JuliaFunction, setimpl, setname,
  JuliaFunctionSig, parse_docstring, parse_function,
  parse_function_sig, generate_docstring, generate_function,
  concat_expr, replace_symbols, strip_lines,
  Expr0

using Base.Meta: ParseError
using StructEquality
using MLStyle: @match

# Data types
############

const Expr0 = Union{Symbol,Expr}

@struct_hash_equal struct JuliaFunction
  name::Expr0
  args::Vector{Expr0}
  kwargs::Vector{Expr0}
  whereparams::Vector{Expr0}
  return_type::Union{Expr0,Nothing}
  impl::Union{Expr,Nothing}
  doc::Union{String,Nothing}
  
  function JuliaFunction(name::Expr0, args=Expr0[], kwargs=Expr0[], whereparams=Expr0[],
                         return_type=nothing, impl=nothing, doc=nothing)
    new(name, args, kwargs, whereparams, return_type, impl, doc)
  end

  function JuliaFunction(;name::Expr0, args=Expr0[], kwargs=Expr0[], whereparams=Expr0[],
                         return_type=nothing, impl=nothing, doc=nothing)
    new(name, args, kwargs, whereparams, return_type, impl, doc)
  end
end

setimpl(f::JuliaFunction, impl) =
  JuliaFunction(f.name, f.args, f.kwargs, f.whereparams, f.return_type, impl, f.doc)

setname(f::JuliaFunction, name) =
  JuliaFunction(name, f.args, f.kwargs, f.whereparams, f.return_type, f.impl, f.doc)

@struct_hash_equal struct JuliaFunctionSig
  name::Expr0
  types::Vector{Expr0}
  whereparams::Vector{Expr0}
  function JuliaFunctionSig(name::Expr0, types::Vector, whereparams::Vector{<:Expr0}=Expr0[])
    new(name, types, whereparams)
  end
end

"""For comparing JuliaFunctionSigs modulo the where parameters"""
@struct_hash_equal struct JuliaFunctionSigNoWhere 
  name::Expr0
  types::Vector{Expr0}
end
JuliaFunctionSigNoWhere(f::JuliaFunctionSig) =
  JuliaFunctionSigNoWhere(f.name, f.types)

JuliaFunctionSig(f::JuliaFunctionSigNoWhere) = JuliaFunctionSig(f.name, f.types)

# Parsing Julia functions
#########################

""" Parse Julia expression that is (possibly) annotated with docstring.
"""
function parse_docstring(expr::Expr)::Tuple{Union{String,Nothing},Expr}
  expr = strip_lines(expr)
  if expr.head == :macrocall && (
      # XXX: It seems that the @doc macro can show up in two forms.
      expr.args[1] == GlobalRef(Core, Symbol("@doc")) ||
      expr.args[1] == Expr(:core, Symbol("@doc")))
    (expr.args[2], expr.args[3])
  else
    (nothing, expr)
  end
end

""" Parse Julia function definition into standardized form.
"""
function parse_function(expr::Expr, default_type=:Any)::JuliaFunction
  doc, expr = parse_docstring(expr)
  fun_expr, impl = @match expr begin
    Expr(:(=), args...) => args
    Expr(:function, args...) => args
    _ => throw(ParseError("Ill-formed function definition $expr"))
  end
  fun_head, whereparams = @match fun_expr begin
    Expr(:where, fun_head, whereparams...) => (fun_head, whereparams)
    _ => (fun_expr, Expr0[])
  end
  (call_expr, return_type, impl, doc) = @match fun_head begin
    Expr(:(::), Expr(:call, args...), return_type) =>
      (Expr(:call, args...), return_type, impl, doc)
    Expr(:call, args...) =>
      (Expr(:call, args...), nothing, impl, doc)
    _ => throw(ParseError("Ill-formed function header $fun_head"))
  end
  (name, args, kwargs) = @match call_expr begin
    Expr(:call, name, Expr(:parameters, kwargs...), args...) => (name, args, kwargs)
    Expr(:call, name, args...) => (name, args, Expr0[])
    _ => throw(ParseError("Ill-formed call expression $call_expr"))
  end
  args = map(args) do arg
    @match arg begin
      Expr(:(::), x, T) => arg
      x::Symbol => :($x::$(default_type))
      Expr(:(::), T) => Expr(:(::), gensym(), T)
      _ => throw(ParseError("Ill-formed argument expression $arg"))
    end
  end
  JuliaFunction(name, args, kwargs, whereparams, return_type, impl, doc)
end

""" Parse signature of Julia function.
"""
function parse_function_sig(fun::JuliaFunction)::JuliaFunctionSig
  types = map(fun.args) do expr
    @match expr begin
      Expr(:(::), _, type) => type
      Expr(:(::), type) => type
      _ => :Any
    end
  end
  JuliaFunctionSig(fun.name, types, fun.whereparams)
end

""" Wrap Julia expression with docstring.
"""
function generate_docstring(expr::Expr, doc::Union{String,Nothing})::Expr
  if isnothing(doc)
    expr
  else
    Expr(:macrocall, GlobalRef(Core, Symbol("@doc")),
         LineNumberNode(0), doc, expr)
  end
end

""" Generate Julia expression for function definition.
"""
function generate_function(fun::JuliaFunction; rename=n->n)::Expr
  kwargsblock = if !isempty(fun.kwargs)
    [Expr(:parameters, fun.kwargs...)]
  else
    []
  end
  call_expr = Expr(:call, rename(fun.name), kwargsblock..., fun.args...)

  if !isnothing(fun.return_type)
    call_expr = Expr(:(::), call_expr, fun.return_type)
  end

  head = if isempty(fun.whereparams)
    call_expr
  else
    Expr(:where, call_expr, fun.whereparams...)
  end

  body = if isnothing(fun.impl)
    Expr(:block)
  else
    # Wrap implementation inside block if not already.
    impl = fun.impl
    impl.head == :block ? impl : Expr(:block, impl)
  end
  expr = Expr(:function, head, body)
  generate_docstring(expr, fun.doc)
end

# Operations on Julia expressions
#################################

""" Concatenate two Julia expressions into a block expression.
"""
function concat_expr(expr1::Expr, expr2::Expr)::Expr
  @match (expr1, expr2) begin
    (Expr(:block, a1...), Expr(:block, a2...)) => Expr(:block, a1..., a2...)
    (Expr(:block, a1...), _) => Expr(:block, a1..., expr2)
    (_, Expr(:block, a2...)) => Expr(:block, expr1, a2...)
    _ => Expr(:block, expr1, expr2)
  end
end

""" Replace symbols occurring anywhere in a Julia function (except the name).
"""
function replace_symbols(bindings::AbstractDict, f::JuliaFunction)::JuliaFunction
  JuliaFunction(
    f.name,
    replace_symbols.(Ref(bindings), f.args),
    replace_symbols.(Ref(bindings), f.kwargs),
    replace_symbols.(Ref(bindings), f.whereparams),
    isnothing(f.return_type) ? nothing : replace_symbols(bindings, f.return_type),
    isnothing(f.impl) ? nothing : replace_symbols(bindings, f.impl),
    f.doc
  )
end

""" Replace symbols occuring anywhere in a Julia expression.
"""
function replace_symbols(bindings::AbstractDict, expr)
  recurse(expr) = replace_symbols(bindings, expr)
  @match expr begin
    Expr(head, args...) => Expr(head, map(recurse,args)...)
    sym::Symbol => get(bindings, sym, sym)
    _ => expr
  end
end

""" Remove all LineNumberNodes from a Julia expression.
"""
function strip_lines(expr::Expr; recurse::Bool=false)::Expr
  args = [ x for x in expr.args if !isa(x, LineNumberNode) ]
  if recurse
    args = [ isa(x, Expr) ? strip_lines(x; recurse=true) : x for x in args ]
  end
  Expr(expr.head, args...)
end

end
