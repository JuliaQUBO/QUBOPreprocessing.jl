using Test
using QUBOPreprocessing
import QUBOTools as QT
import QUBODrivers as QD
import MathOptInterface as MOI

const Ext = Base.get_extension(QUBOPreprocessing,:QUBOPreprocessingQUBODriversExt)
@test Ext !== nothing

include("scripted_child.jl")
include("direct.jl")
include("boundaries.jl")

@testset "public QUBODrivers conformance" begin
    QD.test(Ext.SamplerOptimizer;examples=true)
end

include("toqubo.jl")
