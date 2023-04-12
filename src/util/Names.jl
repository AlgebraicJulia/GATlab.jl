module Names
export Name, StrLit, SymLit, Anon, Default

"""
Names are used to label parts of a GAT.

They are used for both human input and output of a GAT, but are not used
internally.
"""
abstract type Name end

struct StrLit <: Name
  name::String
end

"""
We have a symbol wrapper because we get symbols from parsing, and it
is faster to compare symbols than it is to compare strings.
"""
struct SymLit <: Name
  name::Symbol
end

Name(n::String) = StrLit(n)
Name(n::Char) = StrLit(string(n))
Name(n::Symbol) = n == :default ? Default() : SymLit(n)
Name(n::Name) = n

struct Anon <: Name
end

Base.string(n::StrLit) = n.name
Base.string(n::SymLit) = string(n.name)
Base.string(::Anon) = "_"

Base.show(n::SymLit) = string(n)

struct Default <: Name
end

Base.string(::Default) = "_"

end
