export ThPetri, ThPetriFibered

@theory ThPetri begin
  S::TYPE
  T::TYPE
  I(s::S,t::T)::TYPE
  O(s::S,t::T)::TYPE
end

@theory ThPetriFibered begin
  S::TYPE
  T::TYPE
  I::TYPE
  O::TYPE
  is(i::I)::S
  os(o::O)::S
  it(i::I)::T
  ot(o::O)::T
end