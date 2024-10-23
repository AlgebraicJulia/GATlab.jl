module TestMetaUtils

using Test

using Base.Meta: ParseError

using GATlab

strip_all(expr) = strip_lines(expr, recurse=true)
parse_fun(expr) = parse_function(strip_all(expr))

# Function generation
@test (generate_function(JuliaFunction(:f, [:x, :y])) ==
       strip_all(:(function f(x,y) end)))
@test (generate_function(JuliaFunction(:f, [:(x::Int), :(y::Int)], [], [], :Int)) ==
       strip_all(:(function f(x::Int,y::Int)::Int end)))
@test (generate_function(JuliaFunction(:f, [:x], [], [], :Bool, :(isnothing(x)))) ==
       strip_all(:(function f(x)::Bool isnothing(x) end)))

fun_with_docstring_expr = quote
  """Is nothing"""
  function f(x)::Bool
    isnothing(x)
  end
end
@test (strip_all(generate_function(
        JuliaFunction(:f, [:x], [], [], :Bool, :(isnothing(x)), "Is nothing"))) ==
       strip_all(fun_with_docstring_expr).args[1])

# Function parsing
@test_throws ParseError parse_fun(:(f(x,y)))
@test (parse_fun(:(function f(x,y) x end)) ==
  JuliaFunction(:f, [:(x::Any), :(y::Any)], [], [], nothing, strip_all(quote x end)))

@test parse_fun(strip_all(quote
  """ My docstring
  """
  function f(x,y) x end
end).args[1]) == JuliaFunction(:f, [:(x::Any), :(y::Any)], [], [], nothing, strip_all(quote x end), " My docstring\n")

# TODO RHS has LNN between quote and x
@test (parse_fun(:(function f(x::Int,y::Int)::Int x end)) ==
  JuliaFunction(:f, [:(x::Int),:(y::Int)], [], [], :Int, strip_all(quote x end)))

# TODO RHS has LNN between quote and x
@test (parse_fun(:(f(x,y) = x)) ==
  JuliaFunction(:f, [:(x::Any), :(y::Any)], [], [], nothing, strip_all(quote x end)))

sig = JuliaFunctionSig(:f, [:Int,:Int])
@test parse_function_sig(parse_fun(:(function f(x::Int,y::Int)::Int end))) == sig

# Type transformations
bindings = Dict((:r => :R, :s => :S, :t => :T))
@test replace_symbols(bindings, :(foo(x::r,y::s)::t)) == :(foo(x::R,y::S)::T)
@test replace_symbols(bindings, :(foo(xs::Vararg{r}))) == :(foo(xs::Vararg{R}))

@test replace_symbols(bindings, parse_fun(:(f(r,s) = r))) == parse_fun(:(f(R, S) = R))

@test concat_expr(Expr(:block, :a), Expr(:block, :b)) == Expr(:block, :a, :b)

end
