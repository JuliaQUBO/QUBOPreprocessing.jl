using Documenter
using QUBOPreprocessing

makedocs(
    modules=[QUBOPreprocessing],
    sitename="QUBOPreprocessing.jl",
    authors="QUBOPreprocessing contributors",
    format=Documenter.HTML(prettyurls=get(ENV,"CI","false") == "true"),
    pages=["Foundation" => "index.md", "Reversible conditioning" => "workspace.md",
           "Certificates" => "certificates.md", "API" => "api.md"],
    checkdocs=:exports,
    warnonly=false,
)
# Building documentation is separate from hosting. No deploydocs call here.
