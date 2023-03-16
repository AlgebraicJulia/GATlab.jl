module EMatching

# EMatching is the hard part of EGraphs
#
# Here we follow a strategy similar to egg, but modified somewhat for our uses.
#
# We take a pattern, which is a Trm in a Context, and we attempt to find an
# assignment of an enode to each term in the context.
#
# For instance, we might look for the term `(a * b) * c` in the context
# `[a,b,c::U]` or for the term `f ∘ id(a)` in the context
# `[a,b::Ob,f::Hom(a,b)]`.
#
# Note that not all variables in the context are referenced directly in the
# term; i.e. `b` is never referenced. Thus, ematching must take into account both
# terms and types.

end
