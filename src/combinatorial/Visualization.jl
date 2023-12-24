module Visualization 

export render, ScopedNM

using ...Syntax
using ..DataStructs
using ..DataStructs: ScopedNM, Nest, Nested
using ..TypeScopes: partition
using PrettyTables, StructEquality
import ..DataStructs: getvalue
import ...Syntax: headof

# Nested
########

function Base.show(io::IO, ::MIME"text/plain", nestedtype::NestedType)
  print(io, "$(nameof(getsort(nestedtype)))[")
  join(io, Tuple.(getvalue(nestedtype)), ",")
  print(io, "]")
end 

function Base.show(io::IO, m::MIME"text/plain", nestedterm::NestedTerm)
  show(io, m, argsof(nestedterm))
  print(io, "#$(getvalue(nestedterm))")
end

Base.string(n::Nested) = sprint(show, MIME"text/plain"(), n)

# NestedMatrix 
##############
""" Visualize NestedMatrix using HTML """ # (only tested on Macbook)
function render(nm::ScopedNM)
  f = tempname()*".html"
  write(f, renderstr(nm)); run(`bash -c $("open -a \"Google Chrome\" $f")`)
end

function renderstr(nm::ScopedNM)
  """<!DOCTYPE html>
  <html>
  <head>
  <meta content="width=device-width">
  <style>
  table {
    width: 100%;
    border: 1px solid #ddd;
    border-collapse: collapse;
  }
  td {
    padding: 16px;
    border: 5px solid #ddd;
    border-collapse: collapse;
  }
  tr:nth-child(even) {
    background-color: #eee;
    border: 1px solid #ddd;
    border-collapse: collapse;
  }
  </style>
  </head>
  <body>
  $(str_table(getvalue(nm), getcontext(nm), nm.partition))
  </body>
  </html>"""
end

"""Helper function for `render`"""
function str_table(nm::NestedMatrix,
                   ts::Union{Nothing,TypeScope}=nothing,
                   p::Union{Nothing,Vector{Vector{LID}}}=nothing,
                   caption::String="")
  if nm.depth == 0
    "<table><caption>$caption</caption><tr><td>$(string(getvalue(nm)))</td></tr> </table>"
  else
    nextp, currmsg = if isnothing(p)
      nothing => ""
    else  
      p[2:end] => join(map(p[1]) do x 
        n = " $(nameof(ident(ts; lid=x)))::"
        n * str_algast(getvalue(ts[x]))
      end," × ")
    end
    l = length(size(getvalue(nm)))
    z, n, m = if l == 3
      size(getvalue(nm))
    elseif l == 2
      [1, size(getvalue(nm))...]
    elseif l == 1
      1, 1, only(size(getvalue(nm)))
    else
      error("Unexpected shape $(size(getvalue(nm)))")
    end
    body = join(map(1:z) do k
      row = join(map(1:n) do i
        rowelem = join(map(1:m) do j
          idxs = [[j], [i,j], [k,i,j]][l]
          cap = if isnothing(p) 
            string(idxs)
          else 
            "("*join(map(zip(p[1], idxs)) do (x, idx)
            "$(nameof(ts[ident(ts; lid=x)]))=$idx"
          end,", ")*")"
        end
          str_table(getvalue(getvalue(nm))[idxs...], ts, nextp, cap)
        end,"\n")
        "<td style=\"text-align: center;\">$rowelem</td>"
      end,"\n")
      "<tr>$row</tr>"
    end, "\n")
    "<table><caption>$caption $currmsg</caption> $body</table>"
  end
end 

"""Like `show` but ignores colors. For HTML rendering."""
function str_algast(t::AlgAST)::String
  if GATs.isapp(t)
    if isempty(t.body.args)
      nameof(t.body.head) |> string
    else 
      args = join(str_algast.(t.body.args), ",")
      "$(nameof(t.body.head))($args)"
    end
  elseif GATs.isvariable(t)
    nameof(t.body) |> string
  end
end

"""
Enumerate all the leaf elements of the nested matrix along with their indices.
Print as a table.
"""
function Base.show(io::IO, ::MIME"text/plain", nm::ScopedNM)
  table = permutedims(hcat(mk_table(getvalue(nm))...))
  if !isempty(table) 
    pretty_table(io, table; header=[nameof.(getidents(nm.ts)); :val])
  end
end

function mk_table(nm::NestedMatrix{T}, curr = nothing) where T
  curr = isnothing(curr) ? Int[] : curr 
  res = Vector{String}[]
  val = getvalue(nm)
  if val isa Nest
    for i in CartesianIndices(getvalue(val))
      append!(res, mk_table(getvalue(val)[i], [curr; i.I...]))
    end
  else
    push!(res, string.(Union{Int,T}[curr..., val]))
  end
  res
end

function Base.show(io::IO, m::MIME"text/plain", nm::CombinatorialModel)
  for s in [sorts(nm.theory); funsorts(nm.theory)]
    print(io, nameof(headof(s)))
    tc = getvalue(nm.theory[methodof(s)])
    ctx = getcontext(tc)
    if !isempty(ctx)
      print(io, " ")
      show(io, m, ctx)
    end
    if hasfield(typeof(tc), :type)
      print(io, " :: ", tc.type)
    end
    print(io, "\n")
    show(io, m, nm[s])
  end
end

end # module
