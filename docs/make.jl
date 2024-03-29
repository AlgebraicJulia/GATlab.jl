using Documenter
using Literate

@info "Loading GATlab"
using GATlab

# Set Literate.jl config if not being compiled on recognized service.
config = Dict{String,String}()
if !(haskey(ENV, "GITHUB_ACTIONS") || haskey(ENV, "GITLAB_CI"))
  config["nbviewer_root_url"] = "https://nbviewer.jupyter.org/github/AlgebraicJulia/GATlab.jl/blob/gh-pages/dev"
  config["repo_root_url"] = "https://github.com/AlgebraicJulia/GATlab.jl/blob/main/docs"
end

const literate_dir = joinpath(@__DIR__, "..", "examples")
const generated_dir = joinpath(@__DIR__, "src", "examples")

for (root, dirs, files) in walkdir(literate_dir)
  out_dir = joinpath(generated_dir, relpath(root, literate_dir))
  for file in files
    f, l = splitext(file)
    if l == ".jl" && !startswith(f, "_")
      Literate.markdown(joinpath(root, file), out_dir;
        config=config, documenter=true, credit=false)
      Literate.notebook(joinpath(root, file), out_dir;
        execute=true, documenter=true, credit=false)
    end
  end
end

@info "Building Documenter.jl docs"
makedocs(
  modules=[GATlab],
  format=Documenter.HTML(),
  sitename="GATlab.jl",
  doctest=false,
  checkdocs=:none,
  pages=Any[
    "GATlab.jl" => "index.md",
    "Concepts" => Any[
      "concepts/catlab_differences.md",
      "concepts/scopes.md",
      "concepts/theories.md",
      "concepts/models.md",
      "concepts/symbolic_models.md"
    ],
    "Library Reference" => "api.md",
    "Standard Library" => "stdlib.md",
  ]
)

@info "Deploying docs"
deploydocs(
  target="build",
  repo="github.com/AlgebraicJulia/GATlab.jl.git",
  branch="gh-pages"
)
