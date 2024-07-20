module ResourceSharers
export Rhizome, @rhizome, ResourceSharer, @resource_sharer, Variable

using ...Syntax
using ...Util.Dtrys
using ...Util.Dtrys: flatten, node
using ...Syntax.GATs: tcompose
using ...Util
using MLStyle
using OrderedCollections

"""
A state variable.

This is used for both the variables of [`ResourceSharer`](@ref) and the
junctions of [`Rhizome`](@ref).

This simplifies naming, because instead of having tries and an injective
map between them, we can just have a single trie.
"""
struct Variable
  exposed::Bool
  type::AlgType
end

"""
A variable in the interface to an inner box of a rhizome.

Fields:

- `type`: the type of the variable
- `junction`: the junction that the variable is attached to.
"""
struct PortVariable
  type::AlgType
  junction::DtryVar
end

const Interface = Dtry{AlgType}

"""
A rhizome is a variant of a UWD where the underlying cospan is epi-monic.

The mathematical theory is developed within (provide link to Lohmayer-Lynch
paper).

This also differs from the ACSet-based UWDs in the following ways

1. We use tries instead of numbering things sequentially.
2. All of the "functions out" of the tries are handled by just storing data in
the leaves of the tries, rather than having external "column vectors".
So e.g. we would use `Dtry{Int}` rather than a pair of `Dtry{Nothing}`,
`Dict{DtryVar, Int}`.
3. We use an indexed rather than fibered representation for inner ports
on boxes. That is, we have a function Boxes -> Set rather than a function
InnerPorts -> Boxes. Following 2., this is just stored in the leaf nodes
of the trie of boxes, hence `Dtry{Dtry{PortVariable}}`.
4. We don't have separate sets for outer ports and junctions: rather each
junction is marked as "exposed" or not. This simplifies naming. Also see
[`Variable`](@ref).

All of this adds up to a convenient and compact representation.

The namespaces of `boxes` and `junctions` must be disjoint. One way
of enforcing this would be to do something like

```
struct Box
  ports::Dtry{PortVariable}
end

struct Rhizome
  stuff::Dtry{Union{Variable, Box}}
end
```

The only problem is that I'm not sure then what to call the single field in
`Rhizome`. Also, this would require a slight refactor of the rest of the code.
"""
struct Rhizome
  theory::GAT
  mcompose::AlgClosure
  mzero::AlgClosure
  boxes::Dtry{Dtry{PortVariable}}
  junctions::Dtry{Variable}
end

"""
    ocompose(r::Rhizome, rs::Dtry{Rhizome})

This implements the composition operation for the Dtry-multicategory of
rhizomes. This is the better way of doing the [operad of undirected wiring][1].

TODO: add link to arXiv paper on Dtry-multicategories once it goes up.

See [2] for a reference on general T-multicategories, then trust me for now
that Dtry is a cartesian monoid.

[1]: [The operad of wiring diagrams: formalizing a graphical language for
databases, recursion, and plug-and-play circuits](https://arxiv.org/abs/1305.0297)
[2]: [Higher Operads, Higher Categories](https://arxiv.org/abs/math/0305049)
"""
function ocompose(r::Rhizome, rs::Dtry{Rhizome})
  # paired :: Dtry{Tuple{Dtry{PortVariable}, Rhizome}}
  paired = zip(r.boxes, rs)
  boxes = flatten(mapwithkey(Dtry{Dtry{PortVariable}}, paired) do k, (interface, r′)
    # k :: DtryVar
    # interface :: Dtry{PortVariable}
    # r′ :: Rhizome
    # We want to create the new collection of boxes

    map(Dtry{PortVariable}, r′.boxes) do b
      # b :: Dtry{PortVariable}
      map(PortVariable, b) do p
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
    map(Dtry{Variable}, rs) do r′
      internal_junctions = filter(j -> !j.exposed, r′.junctions)
      if isnothing(internal_junctions)
        Dtrys.node(OrderedDict{Symbol, Dtry{Variable}}())
      else
        internal_junctions
      end
    end
  )

  junctions = merge(r.junctions, newjunctions)

  Rhizome(r.theory, r.mcompose, r.mzero, boxes, junctions)
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

TODO: this currently does not support unexposed junctions. We should support
unexposed junctions.

See some examples below:

```
@rhizome ThRing R(a, b) begin
  X(a, b)
  Y(a, c.x = a)
end

@rhizome ThRing Id(a, b) begin
  _(a, b)
end
```

We can interpret the first rhizome as follows:

1. The rhizome has ports that are typed by types within ThRing. Because
`ThRing` has a `default` type, ports that are not explicitly annotated
will be assumed to be of that type.
2. The name of the rhizome is `R`.
3. The namespace for the external ports of the rhizome is `[a, b]`.
As noted in 1., each of these ports is typed with `default`.
"""
macro rhizome(theorymod, head, body)
  # macroexpand `theory` to get the actual theory
  theory = macroexpand(__module__, :($theorymod.Meta.@theory))
  # parse the name and junctions out of `head`
  junctions = OrderedDict{DtryVar, Variable}()
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
  junctions = Dtry(junctions)

  boxes = OrderedDict{DtryVar, Dtry{PortVariable}}()
  # for each line in body, add a box to boxes
  for line in body.args
    (box, args) = @match line begin
      _::LineNumberNode => continue
      Expr(:call, name, args...) => (parse_var(name), args)
    end
    interface = OrderedDict{DtryVar, PortVariable}()
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
    boxes[box] = Dtry(interface)
  end
  :(
    $name = $Rhizome(
      $theory,
      $theorymod.Meta.Constructors.:(+),
      $theorymod.Meta.Constructors.zero,
      $(Dtry(boxes)),
      $(junctions),
    )
  ) |> esc
end

"""
A resource sharer whose variables are namespaced in a trie
and whose update function is symbolic

TODO: there should be a smart constructor that takes an AlgClosure and finds
the right method of it for the variables and params.
"""
struct ResourceSharer
  variables::Dtry{Variable}
  params::AlgType
  # (tcompose(variables[..].type), params) -> tcompose(variables)
  update::AlgMethod
  # output::AlgType
  # (tcompose(variables[..].type), params) -> output
  # observe::AlgClosure
end

"""
A DSL for writing down resource sharers

Example:
```
@resource_sharer ThRing Spring begin
  variables = x, v
  params = k
  update = (state, params) -> (x = state.v, v = -params.k * state.x)
end
```
"""
macro resource_sharer(theory, name, body)
  args = Expr[]

  for line in body.args
    @match line begin
      _ :: LineNumberNode => nothing
      Expr(:(=), arg, val) =>
        push!(args, Expr(:kw, arg, Expr(:quote, val)))
    end
  end

  esc(:($name = $ResourceSharer($theory.Meta.theory; $(args...))))
end

function parse_namespace(theory::GAT, expr::Expr0)
  vs = OrderedDict{DtryVar, AlgType}()
  argexprs = @match expr begin
    Expr(:tuple, args...) => args
    _ => [expr]
  end
  for arg in argexprs
    (vname, typeexpr) = @match arg begin
      vname::Symbol => (vname, :default)
      Expr(:(.), _, _) => (arg, :default)
      Expr(:(::), vname, type) => (vname, type)
    end
    v = parse_var(vname)
    type = fromexpr(theory, typeexpr, AlgType)
    vs[v] = type
  end
  Dtry(vs)
end

function ResourceSharer(theory::GAT; variables::Expr0, params::Expr0, update::Expr0)
  variable_trie = parse_namespace(theory, variables)
  variables = map(Variable, variable_trie) do type
    Variable(true, type)
  end
  param_type = tcompose(parse_namespace(theory, params))
  state_type = tcompose(variable_trie)

  update = begin
    (argexpr, bodyexpr) = @match update begin
      Expr(:(->), args, body) => (args, last(body.args))
    end
    statename, paramname = @match argexpr begin
      Expr(:tuple, s, p) => (s, p)
    end
    args = TypeScope(statename => state_type, paramname => param_type)
    body = fromexpr(GATContext(theory, args), bodyexpr, AlgTerm)
    AlgMethod(args, body, "", LID.([1,2]), state_type)
  end

  ResourceSharer(variables, param_type, update)
end

function Base.show(io::IO, r::ResourceSharer; theory)
  println(io, "ResourceSharer:")
  print(io, "variables = ", map(v -> string(toexpr(theory, v.type)), String, r.variables))
  println(io, "params = ", toexpr(theory, r.params))
  println(io, "update = ")
  show(io, r.update; theory)
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
function pullback(t1::Dtry{AlgType}, t2::Dtry{Tuple{AlgType, DtryVar}}; argname=:x)
  ty1 = tcompose(t1)
  ty2 = tcompose(map(first, t2))
  ctx = TypeScope(argname => ty1)
  x = Var(ident(ctx; name=argname))
  body = tcompose(
    map(AlgTerm, t2) do (_, k)
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
  t1::Dtry{AlgType},
  t2::Dtry{Tuple{AlgType, DtryVar}},
  mcompose::AlgClosure,
  mzero::AlgClosure;
  argname=:x
)
  preimages = Dict{DtryVar, Vector{DtryVar}}()
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
  x = Var(ident(ctx; name=argname))
  body = tcompose(
    mapwithkey(AlgTerm, t1) do k, _
      foldl(
        (term, v) -> first(values(mcompose.methods))(term, x[v]),
        preimages[k];
        init=mzero()
      )
    end
  )
  AlgMethod(ctx, body, "", [LID(1)], ty1)
end

function oapply(r::Rhizome, sharers::Dtry{ResourceSharer})
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

  # full_state : Dtry{Tuple{AlgType, DtryVar}}
  # This is a trie mapping all the variables in all of the systems
  # to their type, and to the variable in the reduced system that they
  # map to
  full_state = flatten(
    mapwithkey(Dtry{Tuple{AlgType, DtryVar}}, zip(r.boxes, sharers)) do b, (interface, sharer)
      mapwithkey(Tuple{AlgType, DtryVar}, sharer.variables) do k, v
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
  add = pushforward(state, full_state, r.mcompose, r.mzero)

  update_ctx = TypeScope(:state => state_type, :params => params)
  statevar, paramsvar = Var.(idents(update_ctx; name=[:state, :params]))

  update_body = add(orig_update(copy(statevar), paramsvar))

  update = AlgMethod(update_ctx, update_body, "", LID.([1, 2]), state_type)

  ResourceSharer(
    variables,
    params,
    update
  )
end

end
