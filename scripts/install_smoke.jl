# Run inside a fresh consumer environment after installing a pinned source SHA.
using Pkg
using QUBOPreprocessing
import QUBOTools as QT

println("Julia: ", VERSION)
println("QUBOPreprocessing: ", pkgversion(QUBOPreprocessing), " at ", pathof(QUBOPreprocessing))
println("QUBOTools: ", pkgversion(QT), " at ", pathof(QT))
Pkg.status()
@assert pkgversion(QUBOPreprocessing) == v"0.1.0"
@assert pkgversion(QT) >= v"0.16.2"
@assert nameof(QUBOPreprocessing) === :QUBOPreprocessing
@assert Base.PkgId(QUBOPreprocessing).uuid == Base.UUID("ce9b04da-6a94-4a97-978a-34bf3f916ed2")
include(joinpath(dirname(dirname(pathof(QUBOPreprocessing))), "examples", "identity.jl"))
Pkg.test("QUBOPreprocessing")
