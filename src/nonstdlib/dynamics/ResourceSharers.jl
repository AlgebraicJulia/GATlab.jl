module ResourceSharers
export Rhizome, @rhizome

using ...Syntax
using ...Syntax.Tries

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
  mapwithkey(r.junctions) do k, j
    print(io, k, "::", j.type)
  end
  println(io, ")")
  mapwithkey(r.boxes) do k, box
    print(io, k, "(")
    mapwithkey(box) do k′, port
      print(io, k′, "::", port.type, " = ", port.junction)
    end
    print(io, ")")
  end
end

"""
A modified version of the relation macro supporting namespacing

```
@rhizome ThRing R(a, b) begin
  X(a, b)
  Y(a, c.x = a)
end
```
"""
macro rhizome(theory, head, expr)
  
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
