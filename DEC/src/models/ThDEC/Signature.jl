using ...DEC: AbstractSort, SortError

using MLStyle

import Base: +, -, *

# Define the sorts in your theory.
# For the DEC, we work with Scalars and Forms, graded objects which can also be primal or dual.
@data Sort <: AbstractSort begin
    Scalar()
    Form(dim::Int, isdual::Bool)
end
export Scalar, Form

dim(f::Form) = f.dim
duality(f::Form) = f.isdual ? "dual" : "primal"

PrimalForm(i::Int) = Form(i, false)
export PrimalForm

DualForm(i::Int) = Form(i, true)
export DualForm

function Base.show(io::IO, ω::Form)
  print(io, ω.isdual ? "DualForm($(dim(ω)))" : "PrimalForm($(dim(ω)))")
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
        (_, Scalar()) || (Scalar(), _) => throw(SortError("Cannot take a wedge product with a scalar"))
        (Form(i1, isdual1), Form(i2, isdual2)) =>
          if isdual1 == isdual2
            if i1 + i2 <= 2
                Form(i1 + i2, isdual1)
            else
                throw(SortError("Can only take a wedge product when the dimensions of the forms add to less than 2: tried to wedge product $i1 and $i2"))
            end
          else
            throw(SortError("Cannot wedge two forms of different dualities: attempted to wedge $(duality(s1)) and $(duality(s2))"))
          end
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
    (Form(i1, isdual1), Form(i2, isdual2)) =>
      if i1 == 1 && i2 ∈ [1,2] && isdual1 == isdual2
        Form(i2 - 1, isdual2)
      else
        # TODO fix this error message
        throw(SortError("Cannot take the interior product of these forms."))
      end
      (Scalar(), _) || (_, Scalar()) => throw(SortError("Cannot take the interior product involving scalars"))
  end
end

function ♯(s::Sort) end

function ♭(s::Sort) end 
