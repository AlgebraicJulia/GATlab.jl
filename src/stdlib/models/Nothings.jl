module Nothings
export NothingC

using ....Models, ...StdTheories

struct NothingC <: Model{Tuple{Nothing, Nothing}}
end

@instance ThCategory{Nothing, Nothing} (;model::NothingC) begin
  Ob(::Nothing) = nothing
  Hom(::Nothing, ::Nothing, ::Nothing) = nothing

  dom(::Nothing) = nothing
  codom(::Nothing) = nothing

  compose(::Nothing, ::Nothing) = nothing
  id(::Nothing) = nothing
end

end
