module ThEmpty
import ..Theories

const empty_theory = Theory(Anon(), Judgment[])

module Types
end

macro theory()
  empty_theory
end

struct T <: Theories.AbstractTheory end

gettheory(::T) = empty_theory

end
