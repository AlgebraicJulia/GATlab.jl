module ResourceSharers
export Rhizome, @rhizome

using ...Syntax
using ...Syntax.Tries
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
  boxes = flatten(mapwithkey(paired) do (k, (interface, r′))
    # k :: TrieVar
    # interface :: Trie{PortVariable}
    # r′ :: Rhizome
    # We want to create the new collection of boxes

    map(r′.boxes) do b
      # b :: Trie{PortVariable}
      map(b) do p
        # p :: PortVariable
        # p.junction :: namespace(b.junctions)
        j = p.junction
        if j.exposed == true
          # If exposed, then use the junction that the port is connected to
          PortVariable(p.type, interface[j].junction)
        else
          # Otherwise, attach to a newly added junction from the rhizome `r′`
          # which is attached at path `k`
          PortVariable(p.type, k * j)
        end
      end
    end
  end)
  # Add all unexposed junctions
  newjunctions = flatten(
    map(rs) do r′
      filter(j -> !j.exposed, r′.junctions)
    end
  )

  junctions = merge(r.junctions, newjunctions)

  Rhizome(boxes, junctions)
end

# TODO: this should just use a `toexpr` method
function Base.show(io::IO, r::Rhizome)
  print(io, "Rhizome(")
  comma = false
  mapwithkey(r.junctions) do k, j
    if comma
      print(io, ", ")
    end
    comma = true
    print(io, k, "::", j.type)
  end
  println(io, ")")
  newline = false
  mapwithkey(r.boxes) do k, box
    if newline
      println(io)
    end
    newline = true
    print(io, k, "(")
    comma = false
    mapwithkey(box) do k′, port
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
      Expr(:(.), _, _) => (jname, :default)
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
      j = junctions[parse_var(junction)]
      interface[v] = PortVariable(j.type, v)
    end
    boxes[box] = Trie(interface)
  end
  Rhizome(Trie(boxes), junctions)
end

struct ResourceSharer
  variables::Trie{Variable}
  params::AlgType
  # (tcompose(variables), params) -> tcompose(variables)
  update::AlgMethod
  # output::AlgType
  # (tcompose(variables), params) -> output
  # observe::AlgClosure
end

end
