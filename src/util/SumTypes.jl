"""
This is a macro for *good*, *ergonomic* sum types for Julia.

No abstract type b.s.: variants are not separate types.

Simple and predictable.

Compatible with MLStyle via @active patterns, so can be used in @match.

```julia
@sum Node{T} begin
  Const(x::T)
  Sum(summands::Vector{Self})
  Product(factors::Vector{Self})
end

typeof(Const{Int}(5)) == Node{Int}
typeof([Sum{Int}([])]) == Node{Int}
```
"""
module SumTypes
export @sum


using MLStyle
include("MyActive.jl") # a patched version of active patterns

using ..MetaUtils

struct TypeArg
  name::Symbol
  upper_bound::Union{Nothing, Expr0}
end

function fromexpr(e, ::Type{TypeArg})
  @match e begin
    T::Symbol => TypeArg(T, nothing)
    :($T <: $ub) => TypeArg(T, ub)
    _ => error("Failed to parse type argument from $e.")
  end
end

function toexpr(t::TypeArg, with_supertype=true)
  if isnothing(t.upper_bound) || !with_supertype
    t.name
  else
    :($(t.name) <: $(t.upper_bound))
  end
end

Base.nameof(t::TypeArg) = t.name

struct BaseType
  name::Symbol
  args::Vector{TypeArg}
end

function fromexpr(e, ::Type{BaseType})
  @match e begin
    T::Symbol => BaseType(T, TypeArg[])
    :($T{$(args...)}) => BaseType(T, fromexpr.(args, Ref(TypeArg)))
    _ => error("Failed to parse type expression from $e")
  end
end

function toexpr(t::BaseType, with_supertypes=true)
  if length(t.args) == 0
    t.name
  else
    :($(t.name){$(toexpr.(t.args, Ref(with_supertypes))...)})
  end
end

struct Field
  name::Symbol
  type::Any
end

function fromexpr(e, ::Type{Field})
  @match e begin
    f::Symbol => Field(f, Any)
    :($f::$T) => Field(f, T)
    _ => error("Failed to parse field expression from $e")
  end
end

function toexpr(f::Field, self_replacement)
  :($(f.name)::$(replace_symbols(Dict(:Self => self_replacement), f.type)))
end

Base.nameof(f::Field) = f.name

struct Variant
  name::Symbol
  internal_name::Symbol
  fields::Vector{Field}
end

function internal_name(base_name::Symbol, variant_name::Symbol)
  # We don't want to gensym, because then revise will complain
  # about redefining structs
  Symbol("##$base_name#$variant_name")
end

function fromexpr(e, ::Type{Variant}, base_name)
  @match e begin
    v::Symbol => Variant(v, internal_name(base_name, v), Field[])
    :($v($(fields...))) => Variant(v, internal_name(base_name, v), fromexpr.(fields, Ref(Field)))
    _ => error("Failed to parse variant from $e")
  end
end

struct SumType
  basetype::BaseType
  variants::Vector{Variant}
  recursive_type_var::Symbol
end

function variant_struct(type::SumType, v::Variant)
  quote
    struct $(v.internal_name){$(toexpr.(type.basetype.args)...), $(type.recursive_type_var)}
      $(toexpr.(v.fields, Ref(type.recursive_type_var))...)
    end
  end
end

function sumtype_struct(type::SumType)
  variant_types = map(type.variants) do v
    :($(v.internal_name){$(toexpr.(type.basetype.args)...), $(toexpr(type.basetype))})
  end
  quote
    struct $(toexpr(type.basetype))
      content::Union{$(variant_types...)}
    end
  end
end

function variant_constructor(type::SumType, v::Variant)
  variant_type = if length(type.basetype.args) == 0
    v.name
  else
    :($(v.name){$(toexpr.(type.basetype.args)...)})
  end

  variant_constructor = if length(type.basetype.args) == 0
    v.name
  else
    :($(v.name){$(nameof.(type.basetype.args)...)})
  end

  quote
    struct $variant_type
      function $variant_constructor(
        $(toexpr.(v.fields, Ref(toexpr(type.basetype)))...)
      ) where {$(toexpr.(type.basetype.args)...)}
        $(toexpr(type.basetype))(
          $(v.internal_name){
            $(nameof.(type.basetype.args)...),
            $(toexpr(type.basetype))
          }(
            $(nameof.(v.fields)...)
          )
        )
      end
    end
  end
end

function variant_matcher(type::SumType, v::Variant, mod, line)
  (good, bad) = if length(v.fields) == 0
    (true, false)
  elseif length(v.fields) == 1
    (:(Some(content.$(nameof(v.fields[1])))), nothing)
  else
    (Expr(:tuple, (:(content.$(nameof(field))) for field in v.fields)...), nothing)
  end
  MyActive.active_def(
    :($(v.name)(t)),
    quote
      if t isa $(type.basetype.name)
        content = t.content
        if content isa $(v.internal_name)
          $good
        else
          $bad
        end
      else
        $bad
      end
    end,
    mod,
    line
  )
end

function match_show_variant(type::SumType, v::Variant)
  fieldnames = nameof.(v.fields)
  inner = if length(fieldnames) == 1
    quote
      print(io, "(")
      show(io, $(only(fieldnames)))
      print(io, ")")
    end
  else
    :(show(io, $(Expr(:tuple, fieldnames...))))
  end
  :($(v.name)($(fieldnames...)) => begin
    show(io, $(v.name))
    $inner
    print(io, "::")
    show(io, $(toexpr(type.basetype, false)))
  end)
end

function show_method(type::SumType)
  quote
    function Base.show(
      io::IO, t::$(toexpr(type.basetype, false))
    ) where {$(toexpr.(type.basetype.args)...)}
      $(MLStyle).@match t begin
        $(match_show_variant.(Ref(type), type.variants)...)
      end
    end
  end
end

macro sum(type_expr, variants)
  basetype = fromexpr(type_expr, BaseType)

  variants = @match variants begin
    Expr(:block, lines...) =>
      Variant[fromexpr(line, Variant, basetype.name) for line in lines if line isa Expr0]
    _ => error("Failed to parse variants from:\n$variants.\nExpected a block.")
  end

  type = SumType(basetype, variants, gensym())

  esc(
    quote
      $(variant_struct.(Ref(type), type.variants)...)

      $(sumtype_struct(type))

      $(variant_constructor.(Ref(type), type.variants)...)

      $(variant_matcher.(Ref(type), type.variants, Ref(__module__), Ref(__source__))...)

      # can't compile the match statement inside this until later
      eval($(show_method)($type))
    end
  )
end

end
