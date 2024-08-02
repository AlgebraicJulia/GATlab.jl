using ...DEC: Var, addcall!, inject_number!
using ...DEC: roe, graph, id # Var{S} accessors

import Base: +, -, *

# These operations create calls on a common egraph. We validate the signature by dispatching the operation on the types using methods we defined in Signature.

## UNARY OPERATIONS

unop_dec = [:∂ₜ, :d, :★, :-, :♯, :♭]
for unop in unop_dec
  @eval begin
    @nospecialize
    function $unop(v::Var{s}) where s
      s′ = $unop(s)
      Var{s′}(roe(v), addcall!(graph(v), $unop, (id(v),)))
    end

    export $unop
  end
end

# Δ is a composite of Hodge star and d
Δ(v::Var{PrimalForm(0)}) = ★(d(★(d(v))))
export Δ

♭♯(v::Var{DualVF()}) = ♯(♭(v))
export ♭♯

## BINARY OPERATIONS

binop_dec = [:+, :-, :*, :∧] 
for binop in binop_dec
  @eval begin
    @nospecialize
    function $binop(v1::Var{s1}, v2::Var{s2}) where {s1, s2}
      roe(v1) === roe(v2) || throw(BinopError($binop))
      s = $binop(s1, s2)
      Var{s}(v1.roe, addcall!(graph(v1), $binop, (id(v1), id(v2))))
    end

    @nospecialize
    $binop(v::Var, x::Number) = $binop(v, inject_number!(roe(v), x))

    @nospecialize
    $binop(x::Number, v::Var) = $binop(inject_number!(roe(v)), x)
    
    export $binop
  end
end

struct BinopError <: Exception
  binop::Symbol
end

Base.showerror(io::IO, e::BinopError) = print(io, "Cannot use '$binop' on variables from different graphs.")
