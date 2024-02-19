module Gatdoc 

using Markdown

export @gatdoc, gatdoc_impl 

function gatdoc_impl(theory)
 
  vec = split(repr(theory), "\n")
  head = popfirst!(vec)
  replace!(line -> startswith(line, "  #=") ? "" : "    " * line, vec)
  string = join(vec, "\n")
  docstring = Markdown.parse("""

  $head

  $string

  """)

  quote
    const theory = $theory
    @doc $docstring theory
  end
end

macro gatdoc(theory)
  gatdoc_impl(theory) |> esc
end

end
