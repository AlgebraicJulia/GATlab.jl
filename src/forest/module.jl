module Forest
export to_forest
using ...Syntax
using ...Syntax.GATs: TrmTypConstructor, AlgAST, MethodApp
using ...Stdlib: ThSet
import ...Models: show_latex, ModelInterface
using ...Util.MetaUtils: generate_function
import Markdown

const nn = "\n\n"
latex(x::String) = "#{$x}"
p(x::String) = "\\p{$x}"
code(x::Union{SubString,String}) = "\\code{$x}"
function writefile(pth, str)
  io = open(pth, "w"); write(io, str); close(io)
end
alphanum(i) = reverse(string(i, base=35))[1:5]

function show_latex(T::GAT, expr::TypeScope)
  body = join(map(getbindings(expr)) do b 
    v = getvalue(b)
    noshow = methodof(bodyof(v)) == methodof(only(ThSet.Meta.theory.sorts))
    string(nameof(b)) * (noshow ? "" : "::$(show_latex(T, v))")
  end,",\\ ")
  "\\dashv [$body]"
end

show_latex(T::GAT, expr::InCtx) = 
  latex(show_latex(T, getvalue(expr)) * show_latex(T, getcontext(expr)))


function show_latex(T::GAT, expr::A) where {A<:AlgAST} 
  show_latex(T, bodyof(expr))
end
show_latex(T::GAT, x::Ident) = nameof(x)


function show_latex(T::GAT, expr::MethodApp)
  binary, head = false, headof(expr)
  if length(argsof(expr)) <= 2
    for x in getidents(T; aliases=true)
      v = getvalue(T[x])
      if v isa Alias && Base.isoperator(nameof(x)) && v.ref == head 
        binary, head = true, x
      end
    end
  end
  if !binary 
    join(["\\mathop{\\mathrm{$(nameof(head))}}",
  (isempty(argsof(expr)) ? [] : ["\\left(",
  join([show_latex(T,arg) for arg in argsof(expr)], ","),
  "\\right)"])...])
  else 
    join(["\\left(", show_latex(T,first(argsof(expr))), 
    "\\mathop{\\mathrm{$(nameof(head))}}",
    show_latex(T,last(argsof(expr))), "\\right)"])
  end
end

function to_forest_model(mod::Module, model::Any)
  stmts = map(mod.Meta.models[model]) do jf 
    str = string(Base.remove_linenums!(generate_function(jf)))
    code(replace(str, r"#=.+=#" => ""))
  end
  "\\title{$(nameof(model))}\n\\taxon{definition}\n\\tag{model}$(join(p.(stmts),nn))"
end


function to_forest(T::GAT, method::Ident, x::TrmTypConstructor)
  is_trm = hasfield(typeof(x), :type)
  ty = is_trm ? ("::"*show_latex(T, x.type)) : ""
  ctx = getcontext(x)
  canonterm = (is_trm ? AlgTerm : AlgType)(x.declaration, method, AlgTerm.(idents(ctx; lid=x.args)))
  "\\title{$(nameof(x.declaration))}\n" *latex(show_latex(T, canonterm) * ty * show_latex(T, ctx))
end

to_forest(T::GAT, n::Ident, ::AlgDeclaration) = "\\title{$(nameof(n))}"

function to_forest(T::GAT, n::Ident, x::Alias)
  "\\title{$(nameof(n))}\n \\p{Alias for \\ref{$(finame(x.ref))}}"
end

function to_forest(T::GAT, ::Ident, x::AlgAccessor)
  "\\title{$(nameof(x.declaration))}"
end 

function to_forest(T::GAT, n::Ident, x::AlgAxiom)
  name = isnothing(nameof(n)) ? "" : "$(nameof(n)): "
  "\\title{$name}\n" * latex(join(show_latex.(Ref(T), x.equands), " = ")*show_latex(T, getcontext(x)))
end


"""Create a UUID for each judgment's Ident"""
finame(x::Ident) =  "$(alphanum(gettag(x).val.value+getlid(x).val))"

"""
Convert a Module (for a theory) into a tree, a definition tree, and a tree 
for each judgment.
"""
function to_forest(mod::Module, path::String; verbose=true)
  T = mod.Meta.theory

  hsh = alphanum(Syntax.TheoryInterface.REVERSE_GAT_MODULE_LOOKUP[mod].val.value)
  verbose && println("$mod $hsh")
  for xs in T.segments.scopes
    for (x, v) in identvalues(xs)
      fi = joinpath(path, "$(finame(x)).tree")
      writefile(fi, to_forest(T, x, v))
    end
  end

  typs = join(map(last.(typecons(T))) do tc
    "\\transclude{$(finame(tc))}"
  end, nn)
  trms = join(map(last.(termcons(T))) do tc
    "\\transclude{$(finame(tc))}"
  end, nn)

  axs = join(map(T.axioms) do x
    "\\transclude{$(finame(x))}"
  end, nn)

  doms = join(map(Syntax.TheoryMaps.THEORY_DOM_LOOKUP[mod]) do m 
    "\\transclude{$(alphanum(hash(m)))}"
  end)
  codoms = join(map(Syntax.TheoryMaps.THEORY_CODOM_LOOKUP[mod]) do m 
    "\\transclude{$(alphanum(hash(m)))}"
  end)

  mods′ = filter(m->nameof(m)!=:Migrator, ModelInterface.GAT_MODEL_LOOKUP[mod])
  mods = join(map(enumerate(mods′)) do (i,m)
    mhsh = alphanum(hash(mod) + i)
    fi = joinpath(path, "$(mhsh).tree")
    writefile(fi, to_forest_model(mod, m))
    "\\transclude{$(mhsh)}"
  end, nn)
  def = """  
\\title{$(nameof(T))}
\\taxon{definition}\n\n
\\subtree{\\title{Type Constructors} \n$typs}\n
\\subtree{\\title{Term Constructors} \n$trms}\n
\\subtree{\\title{Axioms} \n$axs}\n
"""
  writefile(joinpath(path, "$(hsh)_def.tree"), def)

  doc = to_forest(Base.Docs.doc(mod))

  page = """  
\\title{$(nameof(T))}\n\\tag{theory}\n\n $doc
\\scope{  \\put\\transclude/heading{false} 
\\transclude{$(hsh)_def}\n }
\\subtree{\\title{Models}\n \\put\\transclude/expanded{false} $mods}\n
\\subtree{\\title{TheoryMaps} \n
\\subtree{\\title{As domain} \\put\\transclude/expanded{false} $doms}\n
\\subtree{\\title{As codomain} \\put\\transclude/expanded{false} $codoms}}\n
"""
  writefile(joinpath(path, "$hsh.tree"), page)

end

"""
Convert a theory map into a tree for the definition nested inside 
a general tree for the theory map.
"""
function to_forest_map(mod::Module, path::String)
  M = mod.MAP
  hsh = alphanum(hash(mod))
  typs, trms = map([typemap,termmap]) do fmap 
    join(map(collect(pairs(fmap(M)))) do (k, tic)
      tc = getvalue(M.dom[k])
      decl = tc.declaration
      blck = join(p.(["[$(nameof(decl))]($(finame(decl))):", 
                   latex(show_latex(M.dom, TermInCtx(M.dom, k))), 
                   latex(show_latex(M.codom, tic))]))
      "\\scope{$blck}"
    end, nn)
  end

  # transcluding leads to infinite forester compilation loop
  scope = p("[$(nameof(M.dom))]($(Syntax.TheoryInterface.REVERSE_GAT_MODULE_LOOKUP[mod.dom].val.value|> alphanum)) #{\\rightarrow} [$(nameof(M.codom))]($(Syntax.TheoryInterface.REVERSE_GAT_MODULE_LOOKUP[mod.codom].val.value |> alphanum))")

  def = """  
\\title{$(nameof(mod))}\n\\tag{theorymap}
\\taxon{definition}\n\n$scope
\\subtree{\\title{Type Mapping} \n$typs}\n
\\subtree{\\title{Term Mapping} \n$trms}\n
"""
  writefile(joinpath(path, "$(hsh).tree"), def)
end 

"""
Create a forest in a directory based on all user-declared theories, theorymaps, 
and models
"""
function to_forest(path::String; clear=false, verbose=true)
  ispath(path) && clear && rm.(joinpath.(path, readdir(path)))
  for T in values(Syntax.TheoryInterface.GAT_MODULE_LOOKUP)
    occursin("NonStdlib", string(T)) || to_forest(T, path; verbose)
  end
  to_forest_map.(values(Syntax.TheoryMaps.THEORY_MAPS)  , path);
  cp(joinpath(@__DIR__,"gatlab.tree"), joinpath(path,"gatlab.tree"))
  return nothing
end

"""Ad hoc translation for GATlab docstrings to look passable in Forester"""
function to_forest(doc::Markdown.MD)::String
  str = split(string(doc), "\n\n##")[1] # auto docs produces stuff after this point
  res = replace(str, 
    r"```\n((.|\n)*)\n```"=> s"\\code{\1}", # convert ``` ``` codeblocks
    r"`(.+)`"=> s"\\code{\1}" # convert ` ` inline code
    )
  join(p.(string.((split(res, r"\n+"))))) # handle newlines
end

end # module
