module Lists
using StructEquality

export Bwd, Fwd

"""
An internal data structure for implementing Bwd and Fwd

This is normal cons cell, where head comes before tail.

We store the length at each cell because we frequently want to look it up,
and we want to look it up in O(1) instead of O(n)
"""
@struct_hash_equal struct Cons{T}
  head::T
  length::Int
  tail::Union{Cons{T}, Nothing}
  function Cons(head::T, tail::Union{Cons{T}, Nothing}) where {T}
    new{T}(head, _length(tail) + 1, tail)
  end
  function Cons{T}(head::T, tail::Union{Cons{T}, Nothing}) where {T}
    new{T}(head, _length(tail) + 1, tail)
  end
end

_length(cn::Cons) = cn.length
_length(::Nothing) = 0

"""
A "backwards list"

This is a singly-linked list that supports efficient appending to the end.

The head of this list is at index `end`, to support compatibility with other
AbstractVectors.
"""
@struct_hash_equal struct Bwd{T} <: AbstractVector{T}
  contents::Union{Cons{T}, Nothing}
  function Bwd{T}() where {T}
    new{T}(nothing)
  end
  function Bwd(tail::Bwd{T}, head::T) where {T}
    new{T}(Cons{T}(head, tail.contents))
  end
  function Bwd(elts::AbstractVector{T}) where {T}
    foldl(Bwd, elts; init = Bwd{T}())
  end
  function Bwd{T}(cn::Cons{T}) where {T}
    new{T}(cn)
  end
  function Bwd{T}(n::Nothing) where {T}
    new{T}(n)
  end
end

function Base.size(l::Bwd)
  (_length(l.contents),)
end

function Base.getindex(l::Bwd, i::Int)
  if !(i ∈ eachindex(l))
    throw(BoundsError(l, i))
  end
  _getbwdindex(l.contents, length(l) - i)
end

function _getbwdindex(l::Cons, i::Int)
  if i == 0
    l.head
  else
    _getbwdindex(l.tail, i-1)
  end
end

"""
A "forwards list"

This is a singly-linked list that supports efficient appending to the front.

The head of this list is at index `1`
"""
@struct_hash_equal struct Fwd{T} <: AbstractVector{T}
  contents::Union{Cons{T}, Nothing}
  function Fwd{T}() where {T}
    new{T}(nothing)
  end
  function Fwd(head::T, tail::Fwd{T}) where {T}
    new{T}(Cons(head, tail.contents))
  end
  function Fwd(elts::AbstractVector{T}) where {T}
    foldr(Fwd, elts; init = Fwd{T}())
  end
  function Fwd{T}(cn::Cons{T}) where {T}
    new{T}(cn)
  end
  function Fwd{T}(n::Nothing) where {T}
    new{T}(n)
  end
end

function Base.size(l::Fwd)
  (_length(l.contents),)
end

function Base.getindex(l::Fwd, i::Int)
  if !(i ∈ eachindex(l))
    throw(BoundsError(l, i))
  end
  _getindex(l.contents, i)
end

function _getindex(cn::Cons, i::Int)
  if i == 1
    cn.head
  else
    _getindex(cn.tail, i-1)
  end
end

function _reverse(cn::Cons)
  cn′ = nothing
  while !isnothing(cn)
    cn′ = Cons(cn.head, cn′)
    cn = cn.tail
  end
  cn′
end

_reverse(_::Nothing) = nothing


"""
Converts a forward list into a backwards list in O(n).

We need to call this sometimes so that we don't end up with quadratic
algorithms.
"""
Fwd(bl::Bwd{T}) where {T} = Fwd{T}(_reverse(bl.contents))

Bwd(fl::Fwd{T}) where {T} = Bwd{T}(_reverse(fl.contents))

struct IterInit
end

function Base.iterate(l::Bwd, state=IterInit())
  iterate(Fwd(l), state)
end

function Base.iterate(l::Fwd, state=IterInit())
  iterate(l.contents, state)
end

function Base.iterate(cn::Cons, state=IterInit())
  if state == IterInit()
    (cn.head, cn.tail)
  elseif isnothing(state)
    nothing
  else
    (state.head, state.tail)
  end
end

function Base.iterate(n::Nothing, state=IterInit())
  nothing
end

"""
This makes the list reverse(l1) ++ l2 (if we interpret the cons as a fwd list)
"""
function revcat(l1::Cons{T}, l2::Cons{T}) where {T}
  foldl((t,h) -> Cons(h,t), l1; init=l2)
end

"""
Appends the two lists. The runtime is linear in length of l1.
"""
function append(l1::Fwd{T}, l2::Fwd{T}) where {T}
  if isnothing(l1.contents)
    return l2
  elseif isnothing(l2.contents)
    return l1
  end
  Fwd{T}(revcat(_reverse(l1.contents), l2.contents))
end

"""
Appends the two lists. The runtime is linear in the length of l2
"""
function append(l1::Bwd{T}, l2::Bwd{T}) where {T}
  if length(l1) == 0
    return l2
  elseif length(l2) == 0
    return l1
  end
  Bwd{T}(revcat(_reverse(l2.contents), l1.contents))
end

"""
Concatenates all of the lists in ls. We use a right fold because append is
linear in the length of the left argument, and the right argument is the one
that is growing here.
"""
function Base.vcat(ls::Fwd{T}...) where {T}
  foldr(append, ls; init=Fwd{T}())
end

"""
Concatenates all of the lists in ls. We use a left fold because append is
linear in the length of the left argument, and the left argument is the one
that is growing here.
"""
function Base.vcat(ls::Bwd{T}...) where {T}
  foldl(append, ls; init=Bwd{T}())
end

end
