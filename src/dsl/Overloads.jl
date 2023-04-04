module Overloads

using ...Models
using ...Syntax

TheoryMaps.TheoryIncl(T1::Type{<:AbstractTheory}, T2::Type{<:AbstractTheory}, m) =
  TheoryIncl(theory(T1), theory(T2), m)

Visualization.show_term(T::Type{<:AbstractTheory}, t) = show_term(theory(T), t)
Visualization.show_term(T::Type{<:AbstractTheory}, t, c) = show_term(theory(T), t, c)
Visualization.show_ctx(T::Type{<:AbstractTheory}, c) = show_ctx(theory(T), c)

end
