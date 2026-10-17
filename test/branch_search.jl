include(joinpath(@__DIR__,"..","examples","branch_search.jl"))

@testset "bounded search empty and oversized inputs" begin
    empty_model = QT.Model(Dict{Int,Float64}(),Dict{Tuple{Int,Int},Float64}();offset=2.0)
    result = branch_search(empty_model)
    @test result.state == Int[]
    @test result.energy == 2//1
    @test result.nodes == 1
    oversized = QT.Model(Dict(i=>0.0 for i in 1:9),Dict{Tuple{Int,Int},Float64}())
    @test_throws ArgumentError branch_search(oversized)
end
