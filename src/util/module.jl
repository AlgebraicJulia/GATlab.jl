module Util

using Reexport

include("MetaUtils.jl")
include("HashColor.jl")
include("Eithers.jl")
include("Gatdoc.jl")

@reexport using .MetaUtils
@reexport using .HashColor
@reexport using .Eithers
@reexport using .Gatdoc

end
