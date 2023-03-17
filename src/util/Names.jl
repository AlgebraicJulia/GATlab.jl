module Names
export Name, Literal, Anon

abstract type Name end
struct Literal <: Name
  name::String
end

Name(n::String) = Literal(n)
Name(n::Char) = Literal(string(n))
Name(n::Symbol) = Literal(string(n))
Name(n::Name) = n

struct Anon <: Name
end

Base.string(n::Literal) = n.name
Base.string(::Anon) = " "

end
