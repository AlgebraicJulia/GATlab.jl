""" Finite presentations of a model of a generalized algebraic theory (GAT).

We support two methods for defining models of a GAT: as Julia objects using the
`@instance` macro and as syntactic objects using the `@present` macro.
Instances are useful for casting generic data structures, such as matrices,
abstract tensor systems, and wiring diagrams, in categorical language.
Presentations define small categories by generators and relations and are useful
in applications like knowledge representation.
"""
module Presentations
export @present, Presentation, generator, generators, generator_index,
  has_generator, equations, add_generator!, add_generators!, add_definition!,
  add_equation!, add_equations!

using Base.Meta: ParseError
using MLStyle: @match

import AlgebraicInterfaces: generators
using ...Util.MetaUtils
using ...Syntax
import ...Syntax: equations
using ..SymbolicModels
import ..SymbolicModels: to_json_sexpr, parse_json_sexpr
using ..GATExprUtils


# Data types
############

struct Generators{Name}
  # (name, :Ob) => 1
  # (name, :Hom, :a, :b) => 2
  index::Dict{Tuple{Name, Vector{Symbol}}, Int}
  registry::Dict{Vector{GATExpr}, Vector{Name}} 
end

function Generators{Name}() where Name
  Generators{Name}(
    Dict{Tuple{Name, Vector{Symbol}}, Int}(),
    Dict{Vector{GATExpr}, Vector{Name}}())
end

function index_generators(g::Generators{Name}, name::Symbol; type=[], args=[]) where Name
  filter(g.index) do ((_name, (_type, _args...)), v)
    _name == name && 
    begin !isempty(type) ? _type == [Symbol[];type] : true end &&
    begin !isempty(args) ? _args == args : true end
  end
end

function add_to_index!(g::Generators{Name}, key::Tuple{Name, Vector{Symbol}}, val::Int) where Name
  if haskey(g.index, key)
    push!(g.index[key] => val)
  else
    g.index[key] = val
  end
end

function add_to_registry!(g::Generators{Name}, args::Vector{GATExpr}, name::Name) where Name
  if haskey(g.registry, args)
    if name ∈ g.registry[args]
      error("Name $name already defined in presentation with type $(nameof.(args))")
    else
      push!(g.registry[args], name)
    end
  else
    g.registry[args] = [name]
  end
end

function Base.copy(gens::Generators{Name}) where Name
    Generators{Name}(copy(gens.index), copy(gens.registry))
end

struct Presentation{Theory,Name}
  syntax::Module
  generators::NamedTuple
  generator_name_index::Generators{Name} 
  equations::Vector{Pair}
end

function Presentation{Name}(syntax::Module) where Name
  theory_module = syntax.Meta.theory_module
  theory = theory_module.Meta.theory
  T = theory_module.Meta.T
  names = Tuple(nameof(sort) for sort in sorts(theory))
  vectors = ((getfield(syntax, name){:generator})[] for name in names)
  Presentation{T,Name}(syntax, NamedTuple{names}(vectors), Generators{Name}(), Pair[])
end

Presentation(syntax::Module) = Presentation{Symbol}(syntax)

function Base.:(==)(pres1::Presentation, pres2::Presentation)
  pres1.syntax == pres2.syntax && pres1.generators == pres2.generators &&
    pres1.equations == pres2.equations
end

function Base.copy(pres::Presentation{T,Name}) where {T,Name}
  Presentation{T,Name}(pres.syntax, map(copy, pres.generators),
                       copy(pres.generator_name_index), copy(pres.equations))
end

""" Gets all generators from a Presentation whose name and optionally type signature match.

Usage:

```
index_generators(pres, name) 
```

```
index_generators(pres, name; args=[:A, :B]) 
```

```
index_generators(pres, name; type=:Hom, args=[:A, :B])
```

"""
function index_generators(p::Presentation{Name}, name::Symbol; kwargs...) where Name
  index_generators(p.generator_name_index, name; kwargs...)
end
export index_generators

""" Adds generator to the generator index associated to a Presentation
"""
function add_to_index!(p::Presentation{Name}, args...; kwargs...) where Name
  add_to_index!(p.generator_name_index, args...; kwargs...)
end

""" Adds generator to the generator registry associated to a Presentation
"""
function add_to_registry!(g::Presentation{Name}, args...; kwargs...) where Name
  add_to_registry!(p.generator_Name_index, args...; kwargs...) 
end

# Presentation
##############

""" Get all generators of a presentation.
"""
generators(pres::Presentation) = GATExpr{:generator}[Iterators.flatten(pres.generators)...]
generators(pres::Presentation, type::Symbol) = pres.generators[type]
generators(pres::Presentation, type::Type) = generators(pres, nameof(type))

""" Retrieve generators by name.

Generators can also be retrieved using indexing notation, so that
`generator(pres, name)` and `pres[name]` are equivalent.
"""
function generator(pres::Presentation, name, args=[])
  out = Iterators.map(index_generators(pres.generator_name_index, name; args=args)) do ((name, (type, _...)), index)
    pres.generators[type][index]
  end |> collect
  # safely extract if singleton
  length(out) == 1 ? first(out) : out
end
# TODO what is the intended behavior of this function (and `index_generators`)? 
# Return as many matches, return the first match (`findfirst`), or throw an error?

function Base.getindex(pres::Presentation, name, args...=Symbol[])
  generator.(Ref(pres), name, Ref(args...))
end

""" Does the presentation contain a generator with the given name?
"""
function has_generator(pres::Presentation, name)
  !isempty(index_generators(pres.generator_name_index, name))
end

function get_arg_names(type_arg)
  subargs = join([subarg isa Symbol ? subarg : nameof(args(subarg)) for subarg in type_arg], ",")
  Symbol(join([head(arg), Symbol("("), subargs, Symbol(")")]))
end

""" Add a generator to a presentation.
"""
function add_generator!(pres::Presentation, expr)
  name, type, type_args = first(expr), gat_typeof(expr), gat_type_args(expr)
  generators = pres.generators[type]
  if !isnothing(name)
    add_to_registry!(pres.generator_name_index, type_args, name)
    arg_names = map(type_args) do targ
      try
        nameof(targ)
      catch e
        Symbol(join([head(targ), "(", join(args(targ), ","), ")"]))
      end
    end
    add_to_index!(pres.generator_name_index, (name, [type, arg_names...]), length(generators) + 1)
  end 
  push!(generators, expr)
  expr
end

""" Add iterable of generators to a presentation.
"""
function add_generators!(pres::Presentation, exprs)
  map(exprs) do expr
    add_generator!(pres, expr)
  end
end

""" Get all equations of a presentation.
"""
equations(pres::Presentation) = pres.equations

""" Add an equation between terms to a presentation.
"""
add_equation!(pres::Presentation, lhs::GATExpr, rhs::GATExpr) =
  push!(pres.equations, lhs => rhs)

""" Add sequence of equations to a presentation.
"""
add_equations!(pres::Presentation, eqs) = append!(pres.equations, eqs)

""" Add a generator defined by an equation.
"""
function add_definition!(pres::Presentation, name::Symbol, rhs::GATExpr)
  generator = SymbolicModels.generator_like(rhs, name)
  add_generator!(pres, generator)
  add_equation!(pres, generator, rhs)
  generator
end

""" Get the index of a generator, relative to generators of same GAT type.
"""
function generator_index(pres::Presentation{T,Name}, name::Name, args...) where {T,Name}
  # XXX this destructured binding will effectively `findfirst`
  ((k, v)), = index_generators(pres, name; args=args)
  v
end

function generator_index(pres::Presentation, expr::GATExpr{:generator})
  name = first(expr)
  !isnothing(name) || error("Cannot lookup unnamed generator by name")
  generator_index(pres, name)
end

""" Shorthand for contructing a term in the presentation
"""
function make_term(pres::Presentation, expr)
  @match expr begin
    ::Symbol => pres[expr]
    Expr(:call, term_constructor, args...) =>
      invoke_term(pres.syntax, term_constructor,
                  map(arg -> make_term(pres, arg), args))
  end
end

""" Create a new generator in a presentation of a given type
"""
function make_generator(pres::Presentation, name::Union{Symbol,Nothing},
                        type::Symbol, type_args::Vector)
  invoke_term(pres.syntax, type, [name;
              map(e -> make_term(pres, e), type_args)])
end

""" Create and add a new generator
"""
function construct_generator!(pres::Presentation, name::Union{Symbol,Nothing},
                              type::Symbol, type_args::Vector=[])
  add_generator!(pres, make_generator(pres, name, type, type_args))
end

""" Create and add multiple generators
"""
function construct_generators!(pres::Presentation, names::AbstractVector,
                               type::Symbol, type_args::Vector=[])
  for name in names
    construct_generator!(pres, name, type, type_args)
  end
end

# Presentation Definition
#########################

function add_to_presentation(pres, block)
  pres = copy(pres)
  @match strip_lines(block) begin
    Expr(:block, lines...) =>
      for line in lines
        eval_stmt!(pres, line)
      end
    _ => error("Must pass in a block")
  end
  pres
end

function parse_type_expr(type_expr)
  @match type_expr begin
    Expr(:call, f::Symbol, args...) => (f,[args...])
    f::Symbol => (f,[])
    _ => error("Ill-formed type expression $type_expr")
  end
end

function eval_stmt!(pres::Presentation, stmt::Expr)
  @match stmt begin
    Expr(:(::), name::Symbol, type_expr) =>
      construct_generator!(pres, name, parse_type_expr(type_expr)...)
    Expr(:(::), Expr(:tuple, names...), type_expr) =>
      construct_generators!(pres, [names...], parse_type_expr(type_expr)...)
    Expr(:(::), type_expr) =>
      construct_generator!(pres, nothing, parse_type_expr(type_expr)...)
    Expr(:(:=), name::Symbol, def_expr) =>
      add_definition!(pres, name, make_term(pres, def_expr))
    Expr(:call, :(==), lhs, rhs) =>
      add_equation!(pres, make_term(pres, lhs), make_term(pres, rhs))
  end
end

# Presentation macro
####################

""" Define a presentation using a convenient syntax.
"""
macro present(head, body)
  name, pres = @match head begin
    Expr(:call, name::Symbol, syntax_name::Symbol) =>
      (name, :($(GlobalRef(Presentations, :Presentation))($(esc(syntax_name)))))
    Expr(:(<:), name::Symbol, parent::Symbol) => (name,:(copy($(esc(parent)))))
    _ => throw(ParseError("Ill-formed presentation header $head"))
  end
  quote
    $(esc(name)) = $(esc(add_to_presentation))($pres, $(Expr(:quote, body)))
  end
end

# Serialization
###############

function to_json_sexpr(pres::Presentation, expr::GATExpr)
  to_json_sexpr(expr;
    by_reference = name -> has_generator(pres, name))
end

function parse_json_sexpr(pres::Presentation{Theory,Name},
                          syntax::Module, sexpr) where {Theory,Name}
  parse_json_sexpr(syntax, sexpr;
    symbols = Name == Symbol,
    parse_reference = name -> generator(pres, name))
end

end
