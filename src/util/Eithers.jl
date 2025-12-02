module Eithers
export Either, Left, Right, isleft, isright

using StructEquality

@struct_hash_equal struct Left{T}
  val::T
end

@struct_hash_equal struct Right{S}
  val::S
end

const Either{T, S} = Union{Left{T}, Right{S}}

isleft(::Left) = true
isleft(::Right) = false

isright(::Left) = false
isright(::Right) = true

Base.convert(::Type{Right{S}}, r::Right{T}) where {S, T<:S} =
  Right{S}(r.val)

Base.convert(::Type{Left{S}}, l::Left{T}) where {S, T<:S} =
  Left{S}(l.val)

Base.convert(::Type{Either{A, B}}, right::Right{B′}) where {A, B, B′<:B} = 
  Right{B}(right.val)

Base.convert(::Type{Either{A, B}}, left::Left{A′}) where {A, B, A′<:A} = 
  Left{A}(left.val)

end
