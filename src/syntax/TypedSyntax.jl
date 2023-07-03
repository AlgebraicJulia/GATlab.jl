module TypedSyntax

struct TypedTrm{T<:AbstractTheory, Con<:TrmTag}
  args::Vector{TypedTrm{T}}
end

struct TypedTyp{T<:AbstractTheory, Con<:TypTag}
  args::Vector{TypedTrm{T}}
end

end
