using ...DEC: AbstractSort, SortError

using MLStyle

import Base: +, -, *

# Define the sorts in your theory.
# For the DEC, we work with Scalars and Forms, graded objects which can also be primal or dual.
@data Sort <: AbstractSort begin
  Scalar()
  Form(dim::Int, isdual::Bool)
  VF(isdual::Bool)
end
export Scalar, Form

# accessors
dim(ω::Form) = ω.dim
isdual(ω::Form) = ω.isdual

# convenience functions
PrimalForm(i::Int) = Form(i, false)
export PrimalForm

DualForm(i::Int) = Form(i, true)
export DualForm

PrimalVF() = VF(false)
export PrimalVF

DualVF() = VF(true)
export DualVF

# show methods
show_duality(ω::Form) = isdual(ω) ? "dual" : "primal"

function Base.show(io::IO, ω::Form)
  print(io, isdual(ω) ? "DualForm($(dim(ω)))" : "PrimalForm($(dim(ω)))")
end

## Predicates
function isForm(g, ec::EClass)
  any(ec.nodes) do n
    h = v_head(n)
    if has_constant(g, h)
      c = get_constant(g, h)
      return c isa Form
    end
    false
  end
end


function isForm(g, ec::EClass)
  any(ec.nodes) do n
    h = v_head(n)
    if has_constant(g, h)
      c = get_constant(g, h)
      return c isa Form
    end
    false
  end
end

## OPERATIONS

@nospecialize
function +(s1::Sort, s2::Sort)
  @match (s1, s2) begin
    (Scalar(), Scalar()) => Scalar()
    (Scalar(), Form(i, isdual)) || 
      (Form(i, isdual), Scalar()) => Form(i, isdual)
    (Form(i1, isdual1), Form(i2, isdual2)) =>
      if (i1 == i2) && (isdual1 == isdual2)
        Form(i1, isdual1)
      else
        throw(SortError("Cannot add two forms of different dimensions/dualities: $((i1,isdual1)) and $((i2,isdual2))"))
      end
    end
end

# Type-checking inverse of addition follows addition
-(s1::Sort, s2::Sort) = +(s1, s2)

# TODO error for Forms

# Negation is valid
-(s::Sort) = s

@nospecialize
function *(s1::Sort, s2::Sort)
  @match (s1, s2) begin
    (Scalar(), Scalar()) => Scalar() 
    (Scalar(), Form(i, isdual)) || 
      (Form(i, isdual), Scalar()) => Form(i, isdual)
    (Form(_, _), Form(_, _)) => throw(SortError("Cannot scalar multiply a form with a form. Maybe try `∧`??"))
  end
end

@nospecialize
function ∧(s1::Sort, s2::Sort)
  @match (s1, s2) begin
    (Form(i, isdual), Scalar()) || (Scalar(), Form(i, isdual)) => Form(i, isdual)
    (Form(i1, isdual1), Form(i2, isdual2)) =>
      if i1 + i2 <= 2
        Form(i1 + i2, isdual1)
      else
        throw(SortError("Can only take a wedge product when the dimensions of the forms add to less than 2: tried to wedge product $i1 and $i2"))
      end
    _ => throw(SortError("Can only take a wedge product of two forms"))
  end
end

@nospecialize
∂ₜ(s::Sort) = s

@nospecialize
function d(s::Sort)
  @match s begin
    Scalar() => throw(SortError("Cannot take exterior derivative of a scalar"))
    Form(i, isdual) =>
      if i <= 1
        Form(i + 1, isdual)
      else
        throw(SortError("Cannot take exterior derivative of a n-form for n >= 1"))
      end
  end
end

function ★(s::Sort)
  @match s begin
    Scalar() => throw(SortError("Cannot take Hodge star of a scalar"))
    Form(i, isdual) => Form(2 - i, !isdual)
  end
end

function ι(s1::Sort, s2::Sort)
  @match (s1, s2) begin
    (VF(true), Form(i, true)) => PrimalForm() # wrong
    (VF(true), Form(i, false)) => DualForm()
    _ => throw(SortError("Can only define the discrete interior product on:
            PrimalVF, DualForm(i)
            DualVF(), PrimalForm(i)
            ."))
  end
end

# in practice, a scalar may be treated as a constant 0-form.
function ♯(s::Sort) 
  @match s begin
    Scalar() => PrimalVF()
    Form(1, isdual) => VF(isdual)
    _ => throw(SortError("Can only take ♯ to 1-forms"))
  end
end
# musical isos may be defined for any combination of (primal/dual) form -> (primal/dual) vf.

function ♭(s::Sort) 
  @match s begin
    VF(true) => PrimalForm(1)
    _ => throw(SortError("Can only apply ♭ to dual vector fields"))
  end
end

# OTHER

function ♭♯(s::Sort)
  @match s begin
    Form(i, isdual) => Form(i, !isdual)
    _ => throw(SortError("♭♯ is only defined on forms."))
  end
end

# Δ = ★d⋆d, but we check signature here to throw a more helpful error
function Δ(s::Sort)
  @match s begin
    Form(0, isdual) => Form(0, isdual)
    _ => throw(SortError("Δ is not defined for $s"))
  end
end
