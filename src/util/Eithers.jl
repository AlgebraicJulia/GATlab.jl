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

end
