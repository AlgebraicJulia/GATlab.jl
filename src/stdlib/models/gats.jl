export GATC

using ...Models
using ...Syntax
using ..StdTheories

struct GATC end

@instance ThCategory{GAT, AbsTheoryMap} [model::GATC] begin
  id(x::GAT) = IdTheoryMap(x)
  compose(f::AbsTheoryMap, g::AbsTheoryMap) = TheoryMaps.compose(f,g)
  dom(f::AbsTheoryMap) = TheoryMaps.dom(f)
  codom(f::AbsTheoryMap) = TheoryMaps.codom(f)
end
