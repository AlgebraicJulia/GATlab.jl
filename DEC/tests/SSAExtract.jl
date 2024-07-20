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

extract_ssa!(pode.graph, ssa, (a + b).id, term_select)

ssa

end