
"""
An EGraph has a field `symcache::Dict{Any, Vector{EClassId}}`
whose keys appear to be just symbols (what else could be there?)

To extract a value `a`, we could just index by symcache[a]. 
However, variables could share names. 

Consider this 
```
G = EGraph()
ec1 = addexpr!(G, :(f(a, b)))
ec2 = addexpr!(G, :(f(a, c)))
```
which 
"""
keys(G.symcache)
"""
returns
```
:a => [1]
:b => [2]
:f => [3, 5]
:c => [4]
```
Threading the val for :f into `G.classes`
"""
G.classes[:f]
"""
returns the EClass
```
EClass 3 ([ENode(call, f, Expr, [1,2])], )
```
How do we convert an EClass back to an expression?
"""

"""
``memo::Dict{AbstractENode, EClassId}``
"""