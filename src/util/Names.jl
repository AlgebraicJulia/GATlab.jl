module Names
export Name, StrLit, SymLit, Anon, Default, Annotated

using StructEquality

"""
Names are used to label parts of a GAT.

They are used for both human input and output of a GAT, but are not used
internally.
"""
abstract type Name end

@struct_hash_equal struct StrLit <: Name
  name::String
end

"""
We have a symbol wrapper because we get symbols from parsing, and it
is faster to compare symbols than it is to compare strings.
"""
@struct_hash_equal struct SymLit <: Name
  name::Symbol
end

@struct_hash_equal struct Annotated <: Name
  annotation::Symbol
  name::Name
end

Name(n::String) = StrLit(n)
Name(n::Char) = StrLit(string(n))
Name(n::Symbol) = n == :default ? Default() : SymLit(n)
Name(n::Name) = n
Name(i::Int)= SymLit(Symbol(i))

Name(n; annotation::Symbol) = Annotated(annotation, Name(n))

@struct_hash_equal struct Anon <: Name
end

Base.string(n::StrLit) = n.name
Base.string(n::SymLit) = string(n.name)
Base.string(::Anon) = "_"

Base.show(n::SymLit) = string(n)

@struct_hash_equal struct Default <: Name
end

Base.string(::Default) = "_"

Base.Symbol(n::SymLit) = n.name
Base.Symbol(n::StrLit) = Symbol(n.name)
Base.Symbol(::Anon) = gensym()
Base.Symbol(::Default) = :default

end
