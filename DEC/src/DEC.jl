module DEC

using Reexport

using MLStyle
using Reexport
using StructEquality
import Metatheory
using Metatheory: EGraph, EGraphs, Id, VECEXPR_FLAG_ISCALL, VECEXPR_FLAG_ISTREE, VECEXPR_META_LENGTH
import Metatheory: extract!

import Base: +, -, *

include("util/module.jl") # Pretty-printing
include("roe/module.jl") # Checking signature for DEC operations
include("models/module.jl") # manipulating SSAs 

@reexport using .Util
@reexport using .SSAExtract
@reexport using .Models

end
