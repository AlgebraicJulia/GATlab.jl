module ModelImplementations
export @simple_model

using ...Syntax
using ...Util
using ...Models

macro simple_model(T, name, mod)
  esc(
    Expr(:block,
      __source__,
      :(struct $name <: $(GlobalRef(ModelInterface, :Model)){$T} end),
      :(eval($(GlobalRef(ModelImplementations, :simple_model_impl))($T, $(QuoteNode(name)), $mod)))
    )
  )
end

function simple_model_impl(T::Type{<:AbstractTheory}, name::Symbol, mod::Module)
  t = gettheory(T)
  Expr(:block,
    simple_model_checks(t, name, mod)...,
    simple_model_typargs(t, name, mod)...,
    simple_model_aps(t, name, mod)...
  )
end

function simple_model_checks(t::Theory, name::Symbol, mod::Module)
  defs = Expr[]
  for (i, j) in enumerate(t.judgments)
    if typeof(j.head) == TypCon
      push!(
        defs,
        :($(GlobalRef(ModelInterface, :checkvalidity))(::$name, ::Val{$i}, x) = $mod.check(x))
      )
    end
  end
  defs
end

function simple_model_typargs(t::Theory, name::Symbol, mod::Module)
  defs = Expr[]
  for (i, j) in enumerate(t.judgments)
    if typeof(j.head) == TypCon
      for (l,k) in enumerate(j.head.args)
        (argname, _) = j.ctx[k]
        typeof(argname) = SymLit ||
          error("all arguments to type constructors must be named by symbols to use @simple_model")
        push!(
          defs,
          :($(GlobalRef(ModelInterface, :typarg))(::$name, ::Val{$i}, ::Val{$l}, x) = $mod.$(argname.name)(x))
        )
      end
    end
  end
  defs
end

function simple_model_aps(t::Theory, name::Symbol, mod::Module)
  defs = Expr[]
  for (i, j) in enumerate(t.judgments)
    if typeof(j.head) == TrmCon
      args = Symbol[j.ctx[k][1].name for k in j.head.args]
      tcname = j.name
      typeof(tcname) == SymLit ||
        error("all term constructors must be named by symbols to use @simple_model")
      push!(
        defs,
        :($(GlobalRef(ModelInterface, :ap))(::$name, ::Val{$i}, $(args...)) = $mod.$(tcname.name)($(args...)))
      )
    end
  end
  defs
end

end
