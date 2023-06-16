module MethodInstance 
export @instance

using ...Util
using MLStyle: @match
using ...Syntax


macro instance(head, body)
  theoryname, theoryparams = parse_theory_binding_either(head)
  theory = macroexpand(__module__, :($theoryname.@theory))
  functions, ext_functions = parse_instance_body(body)
  instance_code(theory, theoryparams, functions, ext_functions)
end 


function parse_theory_binding_either(expr::Expr)
  @match expr begin
    Expr(:call, name::Symbol, params...) => (name, params)
    Expr(:curly, name::Symbol, params...) => (name, params)
    _ => throw(ParseError("Ill-formed theory binding $expr"))
  end
end


""" Parse the body of a GAT instance definition.
"""
function parse_instance_body(expr::Expr)
  @assert expr.head == :block
  funs = JuliaFunction[]
  ext_funs = Symbol[]
  for elem in strip_lines(expr).args
    elem = strip_lines(elem)
    head = elem.head
    if head == :macrocall && elem.args[1] == Symbol("@import")
      ext_funs = @match elem.args[2] begin
        sym::Symbol => [ext_funs; [sym]]
        Expr(:tuple, args...) => [ext_funs; Symbol[args...]]
      end
    else
      push!(funs, parse_function(elem))
    end
  end
  return (funs, ext_funs)
end

function instance_code(theory, instance_types, instance_fns, external_fns)
  code = Expr(:block)
  typenames = [Symbol(j.name) for j in theory.judgments if j.head isa TypCon]
  bindings = Dict(zip(typenames, instance_types))
  bound_fns = [ replace_symbols(bindings, f) for f in interface(theory) ]
  bound_fns = OrderedDict(parse_function_sig(f) => f for f in bound_fns)
  instance_fns = Dict(parse_function_sig(f) => f for f in instance_fns)
  for (sig, f) in bound_fns
    if sig.name in external_fns
      continue
    elseif haskey(instance_fns, sig)
      f_impl = instance_fns[sig]
    elseif !isnothing(f.impl)
      f_impl = f
    else
      error("Method $(f.call_expr) not implemented in $(nameof(mod)) instance")
    end
    push!(code.args, generate_function(f_impl))
  end
  return code
end

function interface(T::Theory)::Vector{JuliaFunction}
  [interface(j) for j in judgments(T) if j.head isa TypCon || j.head isa TrmCon
end 
function interface(T::TermCon)::JuliaFunction
end 

end # module
