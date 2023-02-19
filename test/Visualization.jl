module TestVisualization

using Test 
using Gatlab

for th in [ThSet,ThCategory]
  show(devnull,"text/plain", th)
end

end # module
