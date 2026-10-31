# Run inside a fresh consumer environment after installing a pinned source SHA.
using Pkg
using QUBOPreprocessing
import QUBOTools as QT

println("Julia: ", VERSION)
println("QUBOPreprocessing: ", pkgversion(QUBOPreprocessing), " at ", pathof(QUBOPreprocessing))
println("QUBOTools: ", pkgversion(QT), " at ", pathof(QT))
Pkg.status()
@assert pkgversion(QUBOPreprocessing) == v"0.1.5"
@assert pkgversion(QT) >= v"0.16.2"
@assert nameof(QUBOPreprocessing) === :QUBOPreprocessing
@assert Base.PkgId(QUBOPreprocessing).uuid == Base.UUID("ce9b04da-6a94-4a97-978a-34bf3f916ed2")
package_source_root=dirname(dirname(pathof(QUBOPreprocessing)))
for example in ("identity.jl","workspace.jl","certificates.jl","dominance.jl","branch_search.jl")
    # Standalone examples own their globals (including names such as `root`).
    Base.include(Module(gensym(:InstalledExample)),joinpath(package_source_root,"examples",example))
end
# The cheap core installation must not activate the optional solver/compiler stack.
for name in ("QUBODrivers","MathOptInterface","JuMP","ToQUBO")
    @assert all(id.name!=name for id in keys(Base.loaded_modules))
end
Pkg.test("QUBOPreprocessing")
