# GATlab


    EGraphs.jl

    Theories.jl

    TheoryHoms.jl


A theory consists of:
- A parent theory
- a collection of type formers
- a collection of term formers
- a collection of equalities (rewrite formers)

Each type former consists of a context in the parent, i.e. an extension of the parent, and a name and choice of variables in the context that you think of as arguments. The idea is that you should able to infer the context by looking at the arguments.

