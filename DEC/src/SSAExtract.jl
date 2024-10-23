module SSAExtract

using MLStyle
using Metatheory.EGraphs
using ..DEC: Sort
using StructEquality

@struct_hash_equal struct SSAVar
    idx::Int
end

function Base.show(io::IO, v::SSAVar)
    print(io, "%", v.idx)
end

@struct_hash_equal struct SSAExpr
    fn::Any
    args::Vector{Tuple{Sort, SSAVar}}
end

function Base.show(io::IO, e::SSAExpr)
    print(io, e.fn)
    if length(e.args) > 0
        print(io, Expr(:tuple, (Expr(:(::), v, sort) for (sort, v) in e.args)...))
    end
end

"""
Advantages of SSA form:

1. We can preallocate each matrix
2. We can run a register-allocation algorithm to minimize the number of matrices that we have to preallocate
"""
struct SSA
    assignment_lookup::Dict{Id, SSAVar}
    statements::Vector{SSAExpr}
    function SSA()
        new(Dict{Id, SSAVar}(), SSAExpr[])
    end
end

function Base.show(io::IO, ssa::SSA)
    println(io, "SSA: ")
    for (i, expr) in enumerate(ssa.statements)
        println(io, "  ", SSAVar(i), " = ", expr)
    end
end

function add_stmt!(ssa::SSA, id::Id, expr::SSAExpr)
    push!(ssa.statements, expr)
    v = SSAVar(length(ssa.statements))
    ssa.assignment_lookup[id] = v
    v
end

function hasid(ssa::SSA, id::Id)
    haskey(ssa.assignment_lookup, id)
end

function getvar(ssa::SSA, id::Id)
    ssa.assignment_lookup[id]
end

"""
    extract_ssa!(g::EGraph, ssa::SSA, id::Id, term_select, make_expr)::SSAVar

This function adds (recursively) the necessary lines to the SSA in order to
compute a value for `id`, and then returns the SSAVar that the value for `id`
will be assigned to.

The closure parameters control the behavior of this function.

    term_select(id::Id)::VecExpr

This closure selects, given an id in an EGraph, the term that we want to use in
order to compute a value for that id
"""
function extract_ssa!(g::EGraph, ssa::SSA, id::Id, term_select)::SSAVar
    if hasid(ssa, id)
        return getvar(ssa, id)
    end
    term = term_select(id)
    args = map(EGraphs.v_children(term)) do arg
        (g[arg].data, extract_ssa!(g, ssa, arg, term_select))
    end
    add_stmt!(ssa, id, SSAExpr(EGraphs.get_constant(g, EGraphs.v_head(term)), args))
end
export extract_ssa!

function extract_ssa!(g::EGraph, id::Id; ssa::SSA=SSA(), term_select::Function=best_term)
  extract_ssa!(g, ssa, id, term_select)
end

end