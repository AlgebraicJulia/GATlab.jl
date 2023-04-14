"""
This module contains facilities for working with *algebraic* theories, i.e.
theories where none of the type constructors have arguments.

Type inference and checking are much easier for such theories.
"""
module Algebraic

using ...Syntax

"""
Returns whether a theory is algebraic
"""
function is_algebraic(theory::Theory)::Bool
  for j in theory.judgments
    if j.head isa TypCon
      length(j.head.args) == 0 || return false
    end
  end
  true
end

"""
Infer the typ of a trm in an algebraic theory and context.

Throw an error if type cannot be inferred.
"""
function typ_infer(theory::Theory, t::Trm; context::Context = Context())
  if iscontext(t.head)
    context.ctx[index(t.head)][2]
  else
    j = theory.judgments[index(t.head)]
    j.head isa TrmCon || error("head of $t must be a term constructor")
    args = t.args
    length(args) == length(j.head.args) ||
      error("wrong number of args for top-level term constructor in $t")
    argtyps = map(args) do arg
      typ_infer(theory, args; context)
    end
    expected_argtyps = Typ[j.ctx[i][2] for i in j.head.args]
    argtyps == expected_argtyps ||
      error("arguments to $t are wrong type: expected $expected_argtyps, got $argtyps")
    j.head.typ
  end
end

end
