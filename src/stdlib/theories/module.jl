module StdTheories

using Reexport

include("Categories.jl")
include("Algebra.jl")
# include("Monoidal.jl")
# include("Naturals.jl")
# include("Preorders.jl")

@reexport using .Categories
@reexport using .Algebra
# @reexport using .Monoidal
# @reexport using .Naturals
# @reexport using .Preorders

end
