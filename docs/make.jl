using Documenter
using QUBOPreprocessing
using TOML

release_tag=get(ENV,"QUBOPREPROCESSING_RELEASE_TAG","")
release_commit=get(ENV,"QUBOPREPROCESSING_RELEASE_COMMIT","")
if !isempty(release_tag) || !isempty(release_commit)
    occursin(r"^v[0-9]+\.[0-9]+\.[0-9]+$",release_tag) || error("invalid release tag")
    occursin(r"^[0-9a-f]{40}$",release_commit) || error("full release SHA required")
    readchomp(`git -C $(dirname(@__DIR__)) rev-parse HEAD`)==release_commit || error("release checkout mismatch")
    TOML.parsefile(joinpath(dirname(@__DIR__),"Project.toml"))["version"]==release_tag[2:end] || error("release version mismatch")
end
channel=isempty(release_tag) ? "dev" : release_tag
all(arg->arg in ("--skip-deploy","--deploy"),ARGS) || error("unknown documentation argument")
("--skip-deploy" in ARGS && "--deploy" in ARGS) && error("choose build-only or deploy")
deploy="--deploy" in ARGS
if deploy
    get(ENV,"GITHUB_ACTIONS","")=="true" || error("publication requires GitHub Actions")
    isempty(get(ENV,"GITHUB_TOKEN","")) && error("missing publication token")
    get(ENV,"GITHUB_REPOSITORY","")=="JuliaQUBO/QUBOPreprocessing.jl" || error("wrong publisher repository")
    get(ENV,"GITHUB_REF","")=="refs/heads/main" || error("publication requires main")
    get(ENV,"GITHUB_EVENT_NAME","") in ("push","workflow_dispatch") || error("untrusted publication event")
    isempty(release_tag) || get(ENV,"GITHUB_EVENT_NAME","")=="workflow_dispatch" || error("release refresh requires manual dispatch")
    isempty(readchomp(`git -C $(dirname(@__DIR__)) status --porcelain`)) || error("publish only committed source")
end

makedocs(
    modules=[QUBOPreprocessing],
    sitename="QUBOPreprocessing.jl",
    authors="QUBOPreprocessing contributors",
    repo=Documenter.Remotes.GitHub("JuliaQUBO","QUBOPreprocessing.jl"),
    format=Documenter.HTML(prettyurls=true,
        canonical="https://juliaqubo.github.io/QUBOPreprocessing.jl/$channel/",
        edit_link=isempty(release_tag) ? "main" : nothing),
    pages=["Overview" => "index.md", "Reversible conditioning" => "workspace.md",
           "Certificates" => "certificates.md", "Dominance" => "dominance.md",
           "Branch workloads" => "scopes.md", "Optional consumers" => "consumers.md",
           "Operating envelope" => "performance.md", "API" => "api.md"],
    checkdocs=:exports,
    warnonly=false,
)
open(joinpath(@__DIR__,"build","buildinfo.toml"),"w") do io
    TOML.print(io,Dict("package"=>"QUBOPreprocessing","version"=>string(pkgversion(QUBOPreprocessing)),
        "commit"=>readchomp(`git -C $(dirname(@__DIR__)) rev-parse HEAD`),
        "tree"=>readchomp(`git -C $(dirname(@__DIR__)) rev-parse "HEAD^{tree}"`),
        "channel"=>channel,"release_tag"=>release_tag,
        "dirty"=>!isempty(readchomp(`git -C $(dirname(@__DIR__)) status --porcelain`))))
end
if deploy
    # The trusted job stays on main; only Documenter's version router sees
    # the independently validated release tag during this supported call.
    withenv("GITHUB_REF"=>isempty(release_tag) ? "refs/heads/main" : "refs/tags/$release_tag") do
        deploydocs(repo="github.com/JuliaQUBO/QUBOPreprocessing.jl.git",branch="gh-pages",
            devbranch="main",devurl="dev",versions=["stable"=>"v^","v#.#","dev"=>"dev"],
            push_preview=false,forcepush=false)
    end
else
    @info "Build only: no deployment attempted"
end
