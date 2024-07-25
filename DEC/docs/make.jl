using Documenter
using Literate
using Distributed

using DEC

using CairoMakie

# Set Literate.jl config if not being compiled on recognized service.
# config = Dict{String,String}()
# if !(haskey(ENV, "GITHUB_ACTIONS") || haskey(ENV, "GITLAB_CI"))
#   config["nbviewer_root_url"] = "https://nbviewer.jupyter.org/github/AlgebraicJulia/DEC.jl/blob/gh-pages/dev"
#   config["repo_root_url"] = "https://github.com/AlgebraicJulia/Decapodes.jl/blob/main/docs"
# end

const literate_dir = joinpath(@__DIR__, "..", "examples")
const generated_dir = joinpath(@__DIR__, "src", "examples")

@info "Building literate files"
for (root, dirs, files) in walkdir(literate_dir)
  out_dir = joinpath(generated_dir, relpath(root, literate_dir))
  pmap(files) do file
    f,l = splitext(file)
    if l == ".jl" && !startswith(f, "_")
      Literate.markdown(joinpath(root, file), out_dir;
        config=config, documenter=true, credit=false)
      Literate.notebook(joinpath(root, file), out_dir;
        execute=true, documenter=true, credit=false)
    end
  end
end
@info "Completed literate"

pages = Any[]
push!(pages, "DEC.jl"      => "index.md")
push!(pages, "Library Reference" => "api.md")

@info "Building Documenter.jl docs"
makedocs(
  modules   = [DEC],
  format    = Documenter.HTML(
    assets = ["assets/analytics.js"],
  ),
  remotes   = nothing,
  sitename  = "DEC.jl",
  doctest   = false,
  checkdocs = :none,
  pages     = pages)


@info "Deploying docs"
deploydocs(
  target = "build",
  repo   = "github.com/AlgebraicJulia/DEC.jl.git",
  branch = "gh-pages",
  devbranch = "main"
)
