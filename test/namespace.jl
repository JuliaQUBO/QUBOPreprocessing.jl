# The importing module represents a normal consumer session.
module QualifiedOptimizerConsumer
using QUBOPreprocessing
end

@testset "qualified optimizer namespace" begin
    @test !isdefined(QualifiedOptimizerConsumer, :Optimizer)
    @test isdefined(QUBOPreprocessing, :Optimizer)
    @test QualifiedOptimizerConsumer.QUBOPreprocessing.Optimizer === QUBOPreprocessing.Optimizer
end
