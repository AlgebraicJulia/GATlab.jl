module ModelMacros
export @model

using MLStyle
using ...Syntax
using ...Util
using ...Models

using ..Parsing

struct FunctionDef
  name
  args::Vector{Any}
  whereclauses::Vector{Any}
  body
end

# TODO: also support return type
function parsedef(expr)
  @match expr begin
    Expr(:function, Expr(:call, name, args...), body) =>
      FunctionDef(name, Expr0[args...], Expr0[], body)
    Expr(:function, Expr(:where, Expr(:call, name, args...), whereclauses...), body) =>
      FunctionDef(name, Expr0[args...], Expr0[whereclauses...], body)
    Expr(:(=), Expr(:call, name, args...), body) =>
      FunctionDef(name, Expr0[args...], Expr0[], body)
    Expr(:(=), Expr(:where, Expr(:call, name, args...), whereclauses...), body) =>
      FunctionDef(name, Expr0[args...], Expr0[whereclauses...], body)
    _ => nothing
  end
end

function producedef(def::FunctionDef)
  if length(def.whereclauses) > 0
    :(function $(def.name)($(def.args...)) where {$(def.whereclauses...)}
        $(def.body)
      end)
  else
    :(function $(def.name)($(def.args...))
        $(def.body)
      end)
  end
end

"""
Usage:

@model Category{Vector{Int}, Vector{Int}} (self::TypedFinSetC) begin
  ntypes::Int

  Ob(v::Vector{Int}) = all(1 <= j <= self.types for j in v)
  ...
end


@model Category{Int, Matrix{T}} (self::MatC{T<:Num}) begin
  Ob(i::Int) = i >= 0
  Hom(n::Int, m::Int, f::Matrix{T}) = size(f) == (n,m)
  ...
end
"""

macro model(theorydecl, modeldecl, body)
  (T, types) = @match theorydecl begin
    :($T{$(types...)}) => (T, types)
  end

  (self, name, tyargs) = @match modeldecl begin
    :($self::$name{$(tyargs...)}) => (self, name, tyargs)
    :($self::$name) => (self, name, Any[])
  end

  # NOTE: we do not deal with lower bounds on types
  # If we run into a situation where this is important, we need to rethink some things
  stripped_tyargs = map(tyargs) do arg
    @match arg begin
      :($x <: $T) => x
      x => x
    end
  end

  modelarg, modeldef = if length(tyargs) > 0
    (:($self::$name{$(stripped_tyargs...)}), :($name{$(tyargs...)}))
  else
    (:($self::$name), name)
  end

  theory = macroexpand(__module__, :($T.@theory))
  # TODO: check that all methods are defined

  mod = gensym(:Impl)

  @assert body.head == :block

  defs = Dict{Symbol, FunctionDef}()
  fields = Expr0[]

  for line in body.args
    def = parsedef(line)
    if !isnothing(def)
      defs[def.name] = def
    else
      @match line begin
        :($field::$type) => push!(fields, line)
        (field::Symbol) => push!(fields, line)
        _ => nothing
      end
    end
  end

  esc(
    Expr(:block,
         __source__,
         :(struct $modeldef <: $(GlobalRef(ModelInterface, :Model)){$T.Th, Tuple{$(types...)}}
             $(fields...)
           end),
         model_impl(theory, modelarg, stripped_tyargs, defs)
         )
  )
end

function model_impl(t::Theory, model::Expr0, globalwhere::Vector, defs::Dict{Symbol, FunctionDef})
  Expr(:block,
    model_checks(t, model, globalwhere, defs)...,
    model_aps(t, model, globalwhere, defs)...
  )
end

function model_checks(t::Theory, model::Expr0, globalwhere::Vector, defs::Dict{Symbol, FunctionDef})
  out = Expr[]
  for (i, j) in enumerate(t.judgments)
    if typeof(j.head) == TypCon
      def = defs[Symbol(j.name)]
      push!(
        out,
        producedef(
          FunctionDef(
            GlobalRef(ModelInterface, :checkvalidity),
            [model, :(::$(GlobalRef(Theories, :TypTag)){$i}), def.args...],
            [globalwhere; def.whereclauses],
            def.body
          )
        )
      )
    end
  end
  out
end

function model_aps(t::Theory, model::Expr0, globalwhere::Vector, defs::Dict{Symbol, FunctionDef})
  out = Expr[]
  for (i, j) in enumerate(t.judgments)
    if typeof(j.head) == TrmCon
      def = defs[Symbol(j.name)]
      push!(
        out,
        producedef(
          FunctionDef(
            GlobalRef(ModelInterface, :ap),
            [model, :(::$(GlobalRef(Theories, :TrmTag)){$i}), def.args...],
            [globalwhere; def.whereclauses],
            def.body
          )
        )
      )
    end
  end
  out
end

end
