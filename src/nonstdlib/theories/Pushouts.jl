"""
A theory of a category with pushouts highlights two features of 
GATs which require syntactic sugar. The first is an operation 
with a (dependent) record type as its output.

The second is the type of equality witnesses for any given 
AlgSort. This allows us to define functions which are only 
valid when certain *derived terms* from the arguments are 
equal. (E.g. when to apply universal property of a pushout).
"""

export ThPushout

""" Span and CoSpan

The theory for spans and cospans on a category

"""
@theory ThSpanCospan <: ThCategory begin
  struct Span(dom::Ob, codom::Ob)
    apex::Ob
    left::(apex→dom)
    right::(apex→codom)
  end

  struct Cospan(dom::Ob, codom::Ob)
    apex::Ob
    left::(dom→apex)
    right::(codom→apex)
  end
end

"""A category with pushouts"""
@theory ThPushout <: ThSpanCospan begin
  Pushout(s)::TYPE                       ⊣ [(d,c)::Ob, s::Span(d,c)]
  pushout(s)::Pushout(s)                 ⊣ [(d,c)::Ob, s::Span(d,c)] # compute representative
  cospan(p::Pushout(s))::Cospan(d,c)     ⊣ [(d,c)::Ob, s::Span(d,c)] # extract result
  apex(p::Pushout(s)) := cospan(p).apex  ⊣ [(d,c)::Ob, s::Span(d,c)]
  ι₁(p::Pushout(s))   := cospan(p).left  ⊣ [(d,c)::Ob, s::Span(d,c)]
  ι₂(p::Pushout(s))   := cospan(p).right ⊣ [(d,c)::Ob, s::Span(d,c)]
  
  (pushout_commutes :=  (s.left)⋅ι₁(p) == (s.right)⋅ι₂(p)
    ⊣ [(d,c)::Ob, s::Span(d,c), p::Pushout(s)])

  (universal(p, csp, eq) :: (apex(p) → csp.apex)
    ⊣ [(d,c)::Ob, sp::Span(d,c), csp::Cospan(d,c), p::Pushout(sp),
        eq::(sp.left⋅csp.left == sp.right⋅csp.right)])

  ((ι₁(p) ⋅ universal(p, csp, eq) == csp.left)
    ⊣ [(d,c)::Ob, sp::Span(d,c), csp::Cospan(d,c), p::Pushout(sp),
        eq::(sp.left⋅csp.left == sp.right⋅csp.right)])

  ((ι₂(p) ⋅ universal(p, csp, eq) == csp.right)
    ⊣ [(d,c)::Ob, sp::Span(d,c), csp::Cospan(d,c), p::Pushout(sp),
        eq::(sp.left⋅csp.left == sp.right⋅csp.right)])
end

