module Compactify

using ..GATs

export most_recent_backref, compactify_upto

function distance(theory::Theory, ctx::Theory)
  i = 0
  cur = ctx
  while cur != theory
    cur = cur.parent
    i += 1
  end
  i
end

"""
This function returns the lowest deBruijn index into theory
that is referenced in the term constructor termcon.
"""
function most_recent_backref(theory::Theory, termcon::TermCon; greater_than=0)
  min(
    most_recent_backref(theory, termcon.ctx; greater_than),
    most_recent_backref(termcon.typ, greater_than + distance(theory, termcon.ctx))
  )
end

function most_recent_backref(theory::Theory, typecon::TypeCon; greater_than=0)
  most_recent_backref(theory, typecon.ctx; greater_than)
end

function most_recent_backref(theory::Theory, axiom::Axiom; greater_than=0)
  min(
    most_recent_backref(theory, axiom.ctx; greater_than),
    most_recent_backref(theory, axiom.lhs; greater_than),
    most_recent_backref(theory, axiom.rhs; greater_than),
    most_recent_backref(theory, axiom.typ; greater_than)
  )
end

function most_recent_backref(type::TypeInContext, greater_than::Int)
  head = if type.head[1] >= greater_than
    type.head[1]
  else
    typemax(Int)
  end
  args = min(most_recent_backref.(type.args, greater_than)..., typemax(Int))
  min(head, args)
end

function most_recent_backref(term::TermInContext, greater_than::Int)
  head = if term.head[1] >= greater_than
    term.head[1]
  else
    typemax(Int)
  end
  args = min(most_recent_backref.(term.args, greater_than)..., typemax(Int))
  min(head, args)
end

"""
This returns the number of backwards steps one can take from theory before
reaching something that a theory in between theory and ctx refers to.

So if ctx refers to something added in theory, then this returns 0. If
ctx refers to nothing added in theory, but something added in theory.parent,
then this returns 1. And so on.

We use this to figure out whether we can lump theory and ctx together.
"""
function most_recent_backref(theory::Theory, ctx::TheoryExt; greater_than=0)
  intermediates = find_intermediates(theory, ctx)
  mrb = typemax(Int)
  for (i, ctx) in enumerate(intermediates)
    term_mrb = min(most_recent_backref.(Ref(ctx.parent), ctx.termcons; greater_than=i+greater_than-1)..., typemax(Int))
    type_mrb = min(most_recent_backref.(Ref(ctx.parent), ctx.typecons; greater_than=i+greater_than-1)..., typemax(Int))
    axiom_mrb = min(most_recent_backref.(Ref(ctx.parent), ctx.axioms; greater_than=i+greater_than-1)..., typemax(Int))
    mrb = min(min(term_mrb, type_mrb, axiom_mrb) - i + 1, mrb)
  end
  mrb
end

function find_intermediates(theory::Theory, extension::Theory)
  intermediates = Theory[]
  cur = extension
  while cur != theory
    push!(intermediates, cur)
    cur = cur.parent
  end
  reverse!(intermediates)
  intermediates
end

function compactify_upto(theory::Theory, extension::Theory)
  if theory == extension
    return extension
  end
  intermediates = find_intermediates(theory, extension)
  blocks = Vector{Theory}[Theory[intermediates[1]]]
  for t in intermediates[2:end]
    block = blocks[end]
    if most_recent_backref(block[end], t) >= length(block)
      push!(block, t)
    else
      push!(blocks, Theory[t])
    end
  end
  blocks
  # Steps:
  # - compactify the contexts of all typecons/termcons/axioms
  # - concat the typecons/termcons/axioms in each block
  # - fix the deBruijn indices
  #
  # We can fix the deBruijn indices by converting to and then back from linear indices
end

end
