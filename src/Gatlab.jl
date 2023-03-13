module Gatlab
using Reexport

# Util contains code that could be a separate package, but we include in gatlab
# because it's too small to refactor out.
include("util/module.jl")

# Frontend contains the "first pass" of the gatlab compiler. This compiles Julia
# expressions into an organized data structure, but performs absolutely no computation
# or type-checking yet.

# The data structures in Frontend have names that overlap with other parts of Gatlab,
# so these are typically used qualified, like `Frontend.Typ` and `Frontend.Trm`.
include("frontend/module.jl")

# Theories contains a "standard library" of GATs.
include("theories/module.jl")

@reexport using .Util
@reexport using .Theories

end # module Gatlab
