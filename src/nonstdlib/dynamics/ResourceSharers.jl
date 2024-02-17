module ResourceSharers
export Rhizome, @rhizome, ResourceSharer, Variable

using ...Syntax
using ...Syntax.Tries
using ...Syntax.Tries: flatten, node
using ...Syntax.GATs: tcompose
using MLStyle
using OrderedCollections

struct Variable
  exposed::Bool
  type::AlgType
end

struct PortVariable
  type::AlgType
  junction::TrieVar
end

const Interface = Trie{AlgType}

struct Rhizome
  boxes::Trie{Trie{PortVariable}}
  junctions::Trie{Variable}
  function Rhizome(boxes::Trie{Trie{PortVariable}}, junctions::Trie{Variable})
    # TODO: assert that boxes and junctions are disjoint
    # Or alternatively: have a Trie of Union{Interface, Junction}?
    new(boxes, junctions)
  end
end

function ocompose(r::Rhizome, rs::Trie{Rhizome})
  # paired :: Trie{Tuple{Trie{PortVariable}, Rhizome}}
  paired = zip(r.boxes, rs)
  boxes = flatten(mapwithkey(paired) do k, (interface, r′)
    # k :: TrieVar
    # interface :: Trie{PortVariable}
    # r′ :: Rhizome
    # We want to create the new collection of boxes

    map(r′.boxes) do b
      # b :: Trie{PortVariable}
      map(b) do p
        # p :: PortVariable
        # p.junction :: namespace(b.junctions)
        jvar = p.junction
        j = r′.junctions[jvar]
        if j.exposed == true
          # If exposed, then use the junction that the port is connected to
          PortVariable(p.type, interface[jvar].junction)
        else
          # Otherwise, attach to a newly added junction from the rhizome `r′`
          # which is attached at path `k`
          PortVariable(p.type, k * jvar)
        end
      end
    end
  end)
  # Add all unexposed junctions
  newjunctions = flatten(
    map(rs) do r′
      internal_junctions = filter(j -> !j.exposed, r′.junctions)
      if isnothing(internal_junctions)
        Tries.node(OrderedDict{Symbol, Trie{Variable}}())
      else
        internal_junctions
      end
    end
  )

  junctions = merge(r.junctions, newjunctions)

  Rhizome(boxes, junctions)
end

# TODO: this should just use a `toexpr` method
function Base.show(io::IO, r::Rhizome)
  print(io, "Rhizome(")
  comma = false
  traversewithkey(r.junctions) do k, j
    if comma
      print(io, ", ")
    end
    comma = true
    print(io, k, "::", j.type)
  end
  println(io, ")")
  newline = false
  traversewithkey(r.boxes) do k, box
    if newline
      println(io)
    end
    newline = true
    print(io, k, "(")
    comma = false
    traversewithkey(box) do k′, port
      if comma
        print(io, ", ")
      end
      comma = true
      print(io, k′, "::", port.type, " = ", port.junction)
    end
    print(io, ")")
  end
end

function parse_var(e::Union{Expr, Symbol})
  @match e begin
    :_ => PACKAGE_ROOT
    a::Symbol => getproperty(PACKAGE_ROOT, a)
    Expr(:(.), e′, QuoteNode(x)) => parse_var(e′).x
  end
end

"""
A modified version of the relation macro supporting namespacing

```
@rhizome ThRing R(a, b) begin
  X(a, b)
  Y(a, c.x = a)
end

@rhizome ThRing Id(a, b) begin
  _(a, b)
end
```
"""
macro rhizome(theory, head, body)
  # macroexpand `theory` to get the actual theory
  theory = macroexpand(__module__, :($theory.Meta.@theory))
  # parse the name and junctions out of `head`
  junctions = OrderedDict{TrieVar, Variable}()
  (name, args) = @match head begin
    Expr(:call, name::Symbol, args...) => (name, args)
  end
  for arg in args
    (jname, typeexpr) = @match arg begin
      jname::Symbol => (jname, :default)
      Expr(:(.), _, _) => (arg, :default)
      Expr(:(::), jname, type) => (jname, type)
    end
    v = parse_var(jname)
    type = fromexpr(theory, typeexpr, AlgType)
    junctions[v] = Variable(true, type)
  end
  junctions = Trie(junctions)

  boxes = OrderedDict{TrieVar, Trie{PortVariable}}()
  # for each line in body, add a box to boxes
  for line in body.args
    (box, args) = @match line begin
      _::LineNumberNode => continue
      Expr(:call, name, args...) => (parse_var(name), args)
    end
    interface = OrderedDict{TrieVar, PortVariable}()
    for arg in args
      (pname, junction) = @match arg begin
        pname::Symbol => (pname, pname)
        Expr(:(.), _, _) => (arg, arg)
        Expr(:(=), pname, junction) => (pname, junction)
        Expr(:kw, pname, junction) => (pname, junction)
        _ => error("unknown port pattern for box $box: $arg")
      end
      v = parse_var(pname)
      jvar = parse_var(junction)
      j = junctions[jvar]
      interface[v] = PortVariable(j.type, jvar)
    end
    boxes[box] = Trie(interface)
  end
  :(
    $(esc(name)) = $(Rhizome(Trie(boxes), junctions))
  )
end

struct ResourceSharer
  variables::Trie{Variable}
  params::AlgType
  # (tcompose(variables[..].type), params) -> tcompose(variables)
  update::AlgMethod
  # output::AlgType
  # (tcompose(variables[..].type), params) -> output
  # observe::AlgClosure
end

"""
If C is a cartesian category, and t1 and t2 are families of objects in C with a function
of finite sets dom(t2) -> dom(t1), then we can use "copy and delete" to form a morphism in C
from tcompose(t1) to tcompose(t2).

This function implements that operation with the category of AlgTypes.

Arguments
- `t1` is a family of AlgTypes
- `t2` is a family of pairs consisting of an AlgType and a key in `t1`

Produces an AlgMethod going from tcompose(t1) to tcompose(first.(t2))
"""
function pullback(t1::Trie{AlgType}, t2::Trie{Tuple{AlgType, TrieVar}}; argname=:x)
  ty1 = tcompose(t1)
  ty2 = tcompose(map(first, t2))
  ctx = TypeScope(argname => ty1)
  x = AlgTerm(ident(ctx; name=argname))
  body = tcompose(
    map(t2) do (_, k)
      x[k]
    end
  )
  AlgMethod(ctx, body, "", [LID(1)], ty2)
end

"""
If C is a monoidal category with a supply of monoids, and t1 and t2 are families of objects
in C with a function of finite sets dom(t2) -> dom(t1), then we can use the monoid
structure to form a morphism in C from tcompose(t2) to tcompose(t1).

This function implements that operation with the category of AlgTypes, with a user-supplied
monoid operation.

Arguments
- `t1` is a family of AlgTypes
- `t2` is a family of pairs consisting of an AlgType and a key in `t1`

Produces an AlgMethod going from tcompose(first.(t2)) to tcompose(t1)
"""
function pushforward(
  t1::Trie{AlgType},
  t2::Trie{Tuple{AlgType, TrieVar}},
  mcompose::Tuple{Ident, Ident},
  mzero::Tuple{Ident, Ident};
  argname=:x
)
  preimages = Dict{TrieVar, Vector{TrieVar}}()
  traversewithkey(t2) do k, (_, v)
    if haskey(preimages, v)
      push!(preimages[v], k)
    else
      preimages[v] = [k]
    end
  end
  ty1 = tcompose(t1)
  ty2 = tcompose(map(first, t2))
  ctx = TypeScope(argname => ty2)
  x = AlgTerm(ident(ctx; name=argname))
  body = tcompose(
    mapwithkey(t1) do k, _
      foldl(
        (term, v) -> AlgTerm(mcompose..., [term, x[v]]),
        preimages[k];
        init=AlgTerm(mzero..., AlgTerm[])
      )
    end
  )
  AlgMethod(ctx, body, "", [LID(1)], ty1)
end

function oapply(r::Rhizome, sharers::Trie{ResourceSharer}, mcompose, mzero)
  new_variables = filter(v -> !v.exposed, flatten(
    map(sharers) do sharer
      sharer.variables
    end
  ))
  variables = if !isnothing(new_variables)
    merge(r.junctions, new_variables)
  else
    r.junctions
  end
  state = map(v -> v.type, variables)
  state_type = tcompose(state)

  # full_state : Trie{Tuple{AlgType, TrieVar}}
  # This is a trie mapping all the variables in all of the systems
  # to their type, and to the variable in the reduced system that they
  # map to
  full_state = flatten(
    mapwithkey(zip(r.boxes, sharers)) do b, (interface, sharer)
      mapwithkey(sharer.variables) do k, v
        if v.exposed
          (v.type, interface[k].junction)
        else
          (v.type, b * k)
        end
      end
    end
  )

  params = tcompose(map(sharer -> sharer.params, sharers))

  # (full_state, params) -> full_state
  orig_update = tcompose(map(sharer -> sharer.update, sharers), [:state, :params])

  # copy :: state -> full_state
  copy = pullback(state, full_state; argname=:state)

  # add :: full_state -> state
  add = pushforward(state, full_state, mcompose, mzero)

  update_ctx = TypeScope(:state => state_type, :params => params)
  statevar, paramsvar = AlgTerm.(idents(update_ctx; name=[:state, :params]))

  update_body = add(orig_update(copy(statevar), paramsvar))

  update = AlgMethod(update_ctx, update_body, "", LID.([1, 2]), state_type)

  ResourceSharer(
    variables,
    params,
    update
  )
end

end
