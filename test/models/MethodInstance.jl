module TestMethodInstance 
using Gatlab

struct FinSet 
  n::Int 
end
struct FinFunction 
  values::Vector{Int}
  dom::FinSet 
  codom::FinSet 
end 

@instance ThCategory{FinSet,FinFunction} begin 
  dom(f) = f.dom 
  codom(f) = f.codom 
  compose(f,g) = FinFunction(g.values[f.values], dom(f),codom(g)) 
end

end # module
