module TestSSAExtract

using Test
using Metatheory
using DEC

pode = Decapode()

a = fresh!(pode, Scalar(), :a)
b = fresh!(pode, Scalar(), :b)

ssa = SSAExtract.SSA()

function term_select(g::EGraph, id::Id)
    g[id].nodes[1]
end

function make_expr(head, args)
    if length(args) == 0
        SSAExtract.Constant(head)
    else
        SSAExtract.App(head, last.(args))
    end
end

extract_ssa!(pode.graph, ssa, (a + b).id, term_select, make_expr)

end