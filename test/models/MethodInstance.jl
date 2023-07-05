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
  dom(f::FinFunction) = f.dom 
  codom(f::FinFunction) = f.codom 
  id(A::FinSet) = FinFunction(1:A.n, A, A)
  compose(f::FinFunction, g::FinFunction) = FinFunction(g.values[f.values], dom(f),codom(g))
end

A = FinSet(2); 
B=FinSet(3)
f = FinFunction([2,3],A,B)
g = FinFunction([1,1,1],B,A)
id(A)
⋅(f,g)

end # module
