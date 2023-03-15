module EMatching

# EMatching is the hard part of EGraphs
#
# We're going to start with a naive algorithm, similar to backtracking search
# for homomorphism finding.
#
# We have a backtracking state, which is an assignment of variables in the match
# to eclass ids.
#
# Our pattern is a term in a context.
#
# The variables are the elements of the context. So a partial assignment of variables
# to eclass ids is just a vector of Union{Nothing, Id}.

struct Pattern
  ctx::Context
  trm::Trm
end

struct MatchState
  assignment::Vector{Union{Nothing, Id}}
end

function ematch(eg::EGraph, pat::Pattern)
  to_match = [(pat.trm, i) for i in keys(eg.eclasses)]
  state = MatchState([nothing for i in pat.ctx])
  while !isempty(to_match)
    trm, i = pop!(to_match)
  end
end

end
