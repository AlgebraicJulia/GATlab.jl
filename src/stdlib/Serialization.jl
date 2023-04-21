"""
Serialization is fairly straightforward

Terms and types both serialize as

{
  "head": Int
  "args": [term...]
}

A context serializes as

{
  "ctx": [[name, typ]...]
}


"""
module Serialization

export parse_json

import JSON
import JSON.Writer: show_json, begin_object, show_pair, end_object, begin_array, end_array,
  StructuralContext
import JSON.Serializations: StandardSerialization
using MLStyle

using ..StdModels
using ...Syntax
using ...Util

function show_json(io::StructuralContext, s::StandardSerialization, t::Union{Trm, Typ})
  begin_object(io)
  show_pair(io, s, :head => t.head)
  show_pair(io, s, :args => t.args)
  end_object(io)
end

function show_json(io::StructuralContext, s::StandardSerialization, lvl::Lvl)
  begin_object(io)
  show_pair(io, s, :is_context => is_context(lvl))
  show_pair(io, s, :index => index(lvl))
  end_object(io)
end

function show_json(io::StructuralContext, s::StandardSerialization, ctx::Context)
  begin_object(io)
  show_pair(io, s, :ctx => ctx.ctx)
  end_object(io)
end

function show_json(io::StructuralContext, s::StandardSerialization, name::SymLit)
  begin_object(io)
  show_pair(io, s, :type => "SymLit")
  show_pair(io, s, :value => name.name)
  end_object(io)
end

function show_json(io::StructuralContext, s::StandardSerialization, name::StrLit)
  begin_object(io)
  show_pair(io, s, :type => "StrLit")
  show_pair(io, s, :value => name.name)
  end_object(io)
end

function show_json(io::StructuralContext, s::StandardSerialization, name::Default)
  begin_object(io)
  show_pair(io, s, :type => "Default")
  end_object(io)
end

function show_json(io::StructuralContext, s::StandardSerialization, name::Anon)
  begin_object(io)
  show_pair(io, s, :type => "Anon")
  end_object(io)
end

function show_json(io::StructuralContext, s::StandardSerialization, f::KleisliContextMap)
  begin_object(io)
  show_pair(io, s, :dom => f.dom)
  show_pair(io, s, :codom => f.codom)
  show_pair(io, s, :morphism => f.morphism)
  end_object(io)
end

function show_json(io::StructuralContext, s::StandardSerialization, a::SimpleArena)
  begin_object(io)
  show_pair(io, s, :pos => a.pos)
  show_pair(io, s, :dir => a.dir)
  end_object(io)
end

function show_json(io::StructuralContext, s::StandardSerialization, l::SimpleKleisliLens)
  begin_object(io)
  show_pair(io, s, :dom => l.dom)
  show_pair(io, s, :codom => l.codom)
  show_pair(io, s, :expose => l.morphism.expose)
  show_pair(io, s, :update => l.morphism.update)
  end_object(io)
end

function parse_json(d::Dict, ::Type{T}) where {T <: Union{Trm, Typ}}
  T(parse_json(d["head"], Lvl), parse_json.(d["args"], Ref(Trm)))
end

function parse_json(d::Dict, ::Type{Lvl})
  Lvl(d["index"], context=d["is_context"])
end

function parse_json(d::Dict, ::Type{Context})
  Context(parse_json.(d["ctx"], Ref(Tuple{Name, Typ})))
end

function parse_json(d::Vector, ::Type{Tuple{A,B}}) where {A,B}
  (parse_json(d[1], A), parse_json(d[2], B))
end

function parse_json(d::Dict, ::Type{Name})
  @match d["type"] begin
    "SymLit" => SymLit(Symbol(d["value"]))
    "StrLit" => StrLit(d["value"])
    "Default" => Default()
    "Anon" => Anon()
  end
end

function parse_json(v::Vector, ::Type{Vector{T}}) where {T}
  T[parse_json(x, T) for x in v]
end

function parse_json(d::Dict, ::Type{KleisliContextMap})
  KleisliContextMap(
    parse_json(d["dom"], Context),
    parse_json(d["codom"], Context),
    parse_json(d["morphism"], Vector{Trm})
  )
end

function parse_json(d::Dict, ::Type{SimpleArena{T}}) where {T}
  SimpleArena{T}(
    parse_json(d["pos"], Context),
    parse_json(d["dir"], Context)
  )
end

function parse_json(d::Dict, L::Type{SimpleKleisliLens{T}}) where {T}
  SimpleKleisliLens{T}(
    parse_json(d["dom"], SimpleArena{T}),
    parse_json(d["codom"], SimpleArena{T}),
    parse_json(d["expose"], Vector{Trm}),
    parse_json(d["update"], Vector{Trm})
  )
end

end
