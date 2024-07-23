using ...DEC: Var, addcall!

import Base: +, -, *

# These operations create calls on a common egraph. We validate the signature by dispatching the operation on the types using methods we defined in Signature.

@nospecialize
function +(v1::Var{s1}, v2::Var{s2}) where {s1, s2}
    v1.roe === v2.roe || error("Cannot add variables from different graphs")
    s = s1 + s2
    Var{s}(v1.roe, addcall!(v1.roe.graph, +, (v1.id, v2.id)))
end
export +

@nospecialize
+(v::Var, x::Number) = +(v, inject_number!(v.roe, x))

@nospecialize
+(x::Number, v::Var) = +(inject_number!(v.roe, x), v)

@nospecialize
function -(v1::Var{s1}, v2::Var{s2}) where {s1, s2}
    v1.roe == v2.roe || error("Cannot subtract variables from different graphs")
    s = s1 - s2
    Var{s}(v1.roe, addcall!(v1.roe.graph, -, (v1.id, v2.id)))
end
export -

@nospecialize
-(v::Var{s}) where {s} = Var{s}(v.roe, addcall!(v.roe.graph, -, (v.id,)))

@nospecialize
-(v::Var, x::Number) = -(v, inject_number!(v.roe, x))

@nospecialize
-(x::Number, v::Var) = -(inject_number!(v.roe, x), v)

@nospecialize
function *(v1::Var{s1}, v2::Var{s2}) where {s1, s2}
    v1.roe === v2.roe || error("Cannot multiply variables from different graphs")
    s = s1 * s2
    Var{s}(v1.roe, addcall!(v1.roe.graph, *, (v1.id, v2.id)))
end
export *

@nospecialize
*(v::Var, x::Number) = *(v, inject_number!(v.roe, x))

@nospecialize
*(x::Number, v::Var) = *(inject_number!(v.roe, x), v)

@nospecialize
function ∧(v1::Var{s1}, v2::Var{s2}) where {s1, s2}
    v1.roe === v2.roe || error("Cannot wedge variables from different graphs")
    s = s1 ∧ s2
    Var{s}(v1.roe, addcall!(v1.roe.graph, ∧, (v1.id, v2.id)))
end
export ∧

@nospecialize
function ∂ₜ(v::Var{s}) where {s}
    Var{s}(v.roe, addcall!(v.roe.graph, ∂ₜ, (v.id,)))
end
export ∂ₜ

@nospecialize
function d(v::Var{s}) where {s}
    s′ = d(s)
    Var{s′}(v.roe, addcall!(v.roe.graph, d, (v.id,)))
end
export d

@nospecialize
function ★(v::Var{s}) where {s}
    s′ = ★(s)
    Var{s′}(v.roe, addcall!(v.roe.graph, ★, (v.id,)))
end
export ★

Δ(v::Var{PrimalForm(0)}) = ★(d(★(d(v))))
export Δ

# ι
# ♯
# ♭

# end
