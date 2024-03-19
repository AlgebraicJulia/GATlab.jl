julia> using GATlab; @theory ThR begin
           using ThMonoid: ⋅ as *, e as one
       end
[ Info: Any[:((.⋅)), :*]
[ Info: Any[:($(Expr(:., :e))), :one]
┌ Info: After using
│   m.args =
│    2-element Vector{Any}:
│     :(⋅ as *)
└     :(e as one)
