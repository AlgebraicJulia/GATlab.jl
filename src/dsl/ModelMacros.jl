module ModelMacros
export @simple_model

using MLStyle
using ...Syntax
using ...Util
using ...Models

macro simple_model(T, model, body)
  theory = macroexpand(__module__, :($T.@theory))
  # TODO: check that all methods are defined

  mod = gensym(:Impl)

  (name, types) = @match model begin
    :($name{$(types...)}) => (name, types)
  end

  esc(
    Expr(:block,
         __source__,
         :(struct $name <: $(GlobalRef(ModelInterface, :Model)){$T.Th, Tuple{$(types...)}} end),
         Expr(:toplevel,
              :(module $mod
              $body
              end)),
         simple_model_impl(theory, name, mod)
         )
  )
end

function simple_model_impl(t::Theory, name::Symbol, mod::Symbol)
  Expr(:block,
    simple_model_checks(t, name, mod)...,
    simple_model_aps(t, name, mod)...
  )
end

function simple_model_checks(t::Theory, name::Symbol, mod::Symbol)
  defs = Expr[]
  for (i, j) in enumerate(t.judgments)
    if typeof(j.head) == TypCon
      typeof(j.name) == SymLit ||
        error("all type constructors must be named by symbols to use @simple_model")
      args = [gensym(name.name) for (name,_) in j.ctx.ctx]
      push!(
        defs,
        :($(GlobalRef(ModelInterface, :checkvalidity))(::$name, ::$(GlobalRef(Theories, :TypTag)){$i}, $(args...), x) =
          $mod.$(j.name.name)($(args...), x))
      )
    end
  end
  defs
end

function simple_model_aps(t::Theory, name::Symbol, mod::Symbol)
  defs = Expr[]
  for (i, j) in enumerate(t.judgments)
    if typeof(j.head) == TrmCon
      typeof(j.name) == SymLit ||
        error("all term constructors must be named by symbols to use @simple_model")
      args = Symbol[gensym(name.name) for (name,_) in j.ctx.ctx]
      push!(
        defs,
        :($(GlobalRef(ModelInterface, :ap))(::$name, ::$(GlobalRef(Theories, :TrmTag)){$i}, $(args...)) = $mod.$(j.name.name)($(args...)))
      )
    end
  end
  defs
end

end
