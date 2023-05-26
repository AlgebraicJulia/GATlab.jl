module Overloads

using ...Syntax

TheoryMaps.TheoryIncl(T1::Type{<:AbstractTheory}, T2::Type{<:AbstractTheory}, m) =
  TheoryIncl(gettheory(T1), gettheory(T2), m)

Visualization.show_term(T::Type{<:AbstractTheory}, t) = show_term(gettheory(T), t)
Visualization.show_term(T::Type{<:AbstractTheory}, t, c) = show_term(gettheory(T), t, c)
Visualization.show_ctx(T::Type{<:AbstractTheory}, c) = show_ctx(gettheory(T), c)

end
