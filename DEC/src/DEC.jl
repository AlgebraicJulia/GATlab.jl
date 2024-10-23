module DEC
using MLStyle
using Reexport
using StructEquality
import Metatheory
using Metatheory: EGraph, EGraphs, Id, VECEXPR_FLAG_ISCALL, VECEXPR_FLAG_ISTREE, VECEXPR_META_LENGTH
import Metatheory: extract!

import Base: +, -
import Base: *

include("HashColor.jl")
include("Signature.jl")
include("Roe.jl")
include("SSAExtract.jl")
include("Luke.jl")

@reexport using .SSAExtract

end # module DEC
