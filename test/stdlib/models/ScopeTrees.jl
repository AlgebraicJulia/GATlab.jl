module TestScopeTrees

using Test, Gatlab

t = pure(4)

# t = wrap(
#   :a => pure(1),
#   :b => wrap(:x => pure(2), :y => pure(1)),
#   :c => wrap(:f => wrap(:g => pure(4)))
# )

end
