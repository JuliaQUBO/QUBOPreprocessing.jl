# Default equality/hash for a mutable object identifies that particular object.
# Such a key is stable when retained, but an owned deep copy changes identity.
mutable struct IdentityLabel
    name::String
end

# A mutable payload can still have copy-stable key semantics. Payload updates do
# not change label identity, and each snapshot/export must own that payload.
mutable struct ValueLabel
    name::String
    payload::Vector{Int}
end
Base.isequal(a::ValueLabel, b::ValueLabel) = isequal(a.name, b.name)
Base.:(==)(a::ValueLabel, b::ValueLabel) = isequal(a,b)
Base.hash(a::ValueLabel, h::UInt) = hash(a.name,h)

@testset "owned label identity" begin
    badlabels = [IdentityLabel("x"), IdentityLabel("y")]
    bad = QT.Model(badlabels, sparse([1.0,2.0]), spzeros(2,2))
    @test QT.index(bad, badlabels[1]) == 1
    @test_throws ArgumentError Workspace(bad)
    @test_throws ArgumentError preprocess(bad)

    good = QT.Model([:x,:y], sparse([1.0,2.0]), spzeros(2,2))
    ws = Workspace(good)
    token = generation(ws)
    @test_throws ArgumentError reset!(ws,bad)
    @test generation(ws) == token
    @test original_variables(ws) == [:x,:y]
    @test reconstruct(materialize(ws), [1,0]).energy.value == 1.0

    labels = [ValueLabel("y",[1]), ValueLabel("x",[2])]
    source = QT.Model(labels, sparse([1.0,2.0]), spzeros(2,2))
    ws = Workspace(source)
    r = materialize(ws)
    vars = original_variables(r)
    @test vars == labels
    @test hash.(vars) == hash.(labels)
    @test vars == original_variables(r)
    @test vars[1] !== labels[1]
    @test vars[1].payload !== labels[1].payload
    labels[1].payload[1] = 99
    @test original_variables(ws)[1].payload == [1]
    out = export_model(r)
    @test QT.index(out, labels[1]) == 1
    @test QT.variables(out)[1].payload == [1]
    QT.variables(out)[1].payload[1] = 88
    vars[1].payload[1] = 77
    @test original_variables(r)[1].payload == [1]
    @test original_variables(ws)[1].payload == [1]
    @test QT.variables(export_model(r))[1].payload == [1]
end
