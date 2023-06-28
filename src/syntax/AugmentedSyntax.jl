module AugmentedSyntax
export ATrm, ATyp, Const, ATrmCon

using StructEquality
using ..Theories

"""
An augmented typ. This is a typ which might depend on some concrete values.

Because Julia does not support mutually recursive definitions, we have to
declare ahead of time this abstract type, which will only have a single instance
ATyp.
"""
abstract type AbstractATyp end

"""
An augmented trm. This can either be a constant, or a term constructor applied
to augmented trms.
"""
abstract type ATrm end

"""
A constant value in some model, referenced inside an abstract syntax tree.

Contains type information because in general it is impossible to infer the
type.
"""
@struct_hash_equal struct Const <: ATrm
  typ::AbstractATyp
  val::Any
end

"""
A concrete augmented typ, consisting of a typ constructor applied to augmented
trm arguments.
"""
@struct_hash_equal struct ATyp <: AbstractATyp
  head::Lvl
  args::Vector{ATrm}
  function ATyp(l::Lvl, a = ATrm[])
    is_theory(l) || error("Bad head for type: $(index(l))")
    new(l, a)
  end
  function ATyp(l::Int,a=ATrm[])
    new(Lvl(l), a)
  end
end

"""
An augmented term given by applied a term constructor to other augmented terms.
"""
@struct_hash_equal struct ATrmCon <: ATrm
  head::Lvl
  args::Vector{ATrm}
  function ATrmCon(l::Lvl,a=ATrm[])
    is_theory(l) || isempty(a) || error("Elements of context are *nullary* term constructors")
    new(l, a)
  end
  function ATrmCon(l::Int,a=ATrm[])
    new(Lvl(l), a)
  end
end

ATrm(t::Trm) = ATrmCon(t.head, ATrm.(t.args))
ATrm(t::ATrm) = t

ATyp(t::Typ) = ATyp(t.head, ATrm.(t.args))


"""
Plan:

1. Parse augmented terms
2. Interpret/type check augmented terms
3. Serialize/deserialize augmented terms

How do we parse augmented terms? We need to supply a function from Any to
Union{Const, nothing}, that gets called on everything that isn't a symbol or
an expression with head of `:call`.
"""

end # module
