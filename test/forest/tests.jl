module TestForest 
using Test
using GATlab

tmp = joinpath(tempdir(), "forest")
ispath(tmp) || mkdir(tmp)
to_forest(tmp; clear=true, verbose=false)

end