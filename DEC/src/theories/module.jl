module Theories

using Reexport

include("ThDEC/ThDEC.jl") # the theory of the DEC

@reexport using .ThDEC

end
