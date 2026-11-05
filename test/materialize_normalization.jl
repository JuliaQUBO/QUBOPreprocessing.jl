# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

@testset "exact primitive integer export repairs significand loss" begin
    R = Rational{BigInt}
    L = [0.0, 3.0 * 2.0^51, 1.5]
    Q = [0.0 1.5 0.0; 0.0 0.0 0.0; 0.0 0.0 0.0]
    ws = Workspace(fixture([:x, :y, :z], L, Q); integerize_scale=false)
    assume!(ws, :x, 1)
    @test_throws ArgumentError materialize(ws)
    result = materialize(ws; normalization=:integer)
    model = export_model(result)
    @test QT.scale(model) == 1.5
    @test [linear(model)[i] for i in 1:2] == [2.0^52 + 1, 1.0]
    # Derived directly from the input substitution, independently of export.
    expected = [3 * (big(2)^52 + 1) // 2, R(3 // 2)]
    @test [R(QT.scale(model)) * R(linear(model)[i]) for i in 1:2] == expected
    @test result.status === :certified
    @test !result.perturbed && iszero(result.max_perturbation)
    @test !result.certificate.unchanged_representation
    @test index_map(result) == [0, 1, 2]
    @test QT.variables(model) == [:y, :z]
    for y in states(2, :bool)
        lifted = reconstruct(result, y)
        @test lifted.state == [1; y]
        @test exact_model_energy(model, y) == reference(L, Q, 1.0, 0.0, lifted.state, R)
        @test lifted.energy.value == reference(L, Q, 1.0, 0.0, lifted.state)
    end
end

@testset "integer normalization includes mapped fields, couplings and constant" begin
    R = Rational{BigInt}
    # x=(1+s)/2 gives fields ±9/8, coupling 3/8 and constant 3/8.
    # The gauge flips the first field and the coupling.
    L = [1.5, -3.0]
    Q = [0.0 1.5; 0.0 0.0]
    for scale in (-2.0, -0.0, 0.0, 0.5), sense in (:min, :max)
        source = fixture([:x, :y], L, Q; scale, sense, offset=0.75)
        ws = Workspace(source; integerize_scale=false)
        map = domain_map(ws; domain=:spin, gauge=[-1, 1])
        result = materialize(ws, map; normalization=:integer)
        model = export_model(result)
        @test QT.domain(model) === QT.SpinDomain
        @test QT.sense(model) === (sense === :min ? QT.Min : QT.Max)
        @test isequal(QT.scale(model), scale * 0.375)
        @test [linear(model)[i] for i in 1:2] == [-3.0, -3.0]
        @test quadratic(model)[1, 2] == -1.0
        @test QT.offset(model) == 1.0
        @test R(QT.scale(model)) .* R.([-3.0, -3.0, -1.0, 1.0]) ==
            R(scale) .* [-9 // 8, -9 // 8, -3 // 8, 3 // 8]
        @test !result.certificate.unchanged_representation
        for y in states(2, :spin)
            rec = reconstruct(result, y)
            @test rec.state == [(1 - y[1]) ÷ 2, (1 + y[2]) ÷ 2]
            @test exact_model_energy(model, y) == reference(L, Q, scale, 0.75, rec.state, R)
            @test rec.energy.value == reference(L, Q, scale, 0.75, rec.state)
        end
        # Both mutable export models and the source are separate from the
        # retained source objective, coordinate map and normalized payload.
        copied = deepcopy(result)
        @test copied._map !== result._map
        @test result._map !== map
        linear(source)[1] = 99.0
        linear(model)[1] = 99.0
        @test linear(export_model(result))[1] == -3.0
        @test linear(export_model(copied))[1] == -3.0
        @test original_variables(result) == [:x, :y]
        @test index_map(result) == [1, 2]
        @test reconstruct(copied, [-1, 1]).energy.value == reference(L, Q, scale, 0.75, [1, 1])
        cp = checkpoint(ws)
        assume!(ws, :y, 0)
        @test reconstruct(result, [-1, 1]).state == [1, 1]
        rollback!(ws, cp)
    end

    # The constant must participate in the gcd. Ignoring 1/2 would choose
    # factor 3/2 here and produce a noninteger constant of 1/3.
    ws = Workspace(fixture([:x], [1.5], zeros(1, 1); offset=0.5); integerize_scale=false)
    model = export_model(materialize(ws; normalization=:integer))
    @test QT.scale(model) == 0.5
    @test linear(model)[1] == 3.0
    @test QT.offset(model) == 1.0

    # Coordinate conversion produces quarter-subnormals, which individually
    # underflow. The original scale four makes their common scale representable.
    tiny = nextfloat(0.0)
    ws = Workspace(fixture([:x, :y], zeros(2), [0.0 tiny; 0.0 0.0]; scale=4.0);
                   integerize_scale=false)
    map = domain_map(ws; domain=:spin)
    @test_throws ArgumentError materialize(ws, map)
    result = materialize(ws, map; normalization=:integer)
    model = export_model(result)
    @test QT.scale(model) == tiny
    @test [linear(model)[i] for i in 1:2] == [1.0, 1.0]
    @test quadratic(model)[1, 2] == QT.offset(model) == 1.0
    @test !result.perturbed && iszero(result.max_perturbation)
    for y in states(2, :spin)
        rec = reconstruct(result, y)
        @test exact_model_energy(model, y) == reference(zeros(2), [0.0 tiny; 0.0 0.0], 4.0, 0.0, rec.state, R)
    end
end

@testset "integer normalization identity, constants and proof metadata" begin
    R = Rational{BigInt}
    # The identity shortcut must honor normalization even without reductions.
    ws = Workspace(fixture([:x], [1.5], zeros(1, 1)); integerize_scale=false)
    @test materialize(ws) isa ExportResult
    normalized = materialize(ws; normalization=:integer)
    @test normalized isa ConditionedExport{Float64}
    @test linear(export_model(normalized))[1] == 1.0
    @test QT.scale(export_model(normalized)) == 1.5
    @test !normalized.certificate.unchanged_representation
    @test materialize(ws; normalization=:none).certificate.unchanged_representation
    unit_ws = Workspace(fixture([:x], [1.0], zeros(1, 1)))
    @test materialize(unit_ws; normalization=:integer).certificate.unchanged_representation

    # Large even integers can be exact beyond 2^53; a magnitude cutoff would
    # wrongly reject the first primitive coefficient.
    ws = Workspace(fixture([:x, :y], [2.0^54, 1.0], zeros(2, 2)); integerize_scale=false)
    model = export_model(materialize(ws; normalization=:integer))
    @test linear(model)[1] == 2.0^54
    @test linear(model)[2] == QT.scale(model) == 1.0

    for scale in (-2.0, -0.0, 0.0, 0.5)
        ws = Workspace(fixture([:x], [1.5], zeros(1, 1); scale, offset=1.5);
                       integerize_scale=false)
        assume!(ws, :x, 1)
        result = materialize(ws; normalization=:integer)
        model = export_model(result)
        @test QT.dimension(model) == 0
        @test QT.offset(model) == 1.0
        @test isequal(QT.scale(model), scale * 3.0)
        @test exact_model_energy(model, Int[]) == R(scale) * 3
        @test reconstruct(result, Int[]).state == [1]
        @test !result.perturbed

        # Zero polynomial convention: factor one, unchanged source scale.
        zero_ws = Workspace(fixture([:x], zeros(1), zeros(1, 1); scale);
                            integerize_scale=false)
        zero_result = materialize(zero_ws; normalization=:integer)
        @test isequal(QT.scale(export_model(zero_result)), scale)
        @test linear(export_model(zero_result))[1] == QT.offset(export_model(zero_result)) == 0.0
        @test zero_result.certificate.unchanged_representation
        assume!(zero_ws, :x, 0)
        @test isequal(QT.scale(export_model(materialize(zero_ws; normalization=:integer))), scale)
    end

    # Input approximation belongs to the historical proof. Exact export
    # normalization must neither erase it nor record a new rounding error.
    ws = Workspace(fixture([:x, :y], [-0.4, 0.6], [0.0 0.2; 0.0 0.0]); rules=:dominance,
                   integerize_scale=true, max_decimals=1, atol=1e-12)
    @test ws.perturbed && ws.max_perturbation > 0
    @test apply_dominance!(ws, :x).stop_reason === :applied
    result = materialize(ws; normalization=:integer)
    @test result.status === :certified
    @test result.perturbed
    @test result.max_perturbation == ws.max_perturbation
    @test result.certificate.proof.perturbed
    @test result.certificate.proof.max_perturbation == ws.max_perturbation
    @test result._snapshot.scale == result.certificate.proof._source.scale == ws._snapshot.scale
    @test QT.scale(export_model(result)) == 2 * ws._snapshot.scale
    @test verify_certificate(ws, result.certificate.proof).valid
    @test deepcopy(result).max_perturbation == result.max_perturbation
end

@testset "integer normalization fails without exact finite transport" begin
    R = Rational{BigInt}
    ws = Workspace(fixture([:x], [1.0], zeros(1, 1)))
    @test_throws ArgumentError materialize(ws; normalization=:primitive)
    @test_throws ArgumentError materialize(ws; normalization="integer")
    @test_throws ArgumentError materialize(ws; normalization=:integer, rounding=:nearest)
    @test_throws ArgumentError materialize(ws; normalization=:integer, coefficient_type=R)
    @test_throws ArgumentError materialize(ws; normalization=:integer, coefficient_type=Float32)
    map = domain_map(ws; domain=:spin)
    @test_throws ArgumentError materialize(ws, map; normalization=:integer, rounding=:nearest)
    other_ws = Workspace(fixture([:x], [1.0], zeros(1, 1)))
    other_map = domain_map(other_ws; domain=:spin)
    @test_throws ArgumentError materialize(ws, other_map; normalization=:integer)

    # The independent residual fields are [1, 1+2^-53]. Their common
    # denominator is 2^53 and the primitive numerator gcd is one, so the
    # second integer still needs 54 significant bits. Zero scale does not
    # waive exact storage requirements.
    for scale in (1.0, 0.0)
        ws = Workspace(fixture([:x, :y, :z], [0.0, 1.0, 1.0],
            [0.0 0.0 2.0^-53; 0.0 0.0 0.0; 0.0 0.0 0.0]; scale);
            integerize_scale=false)
        assume!(ws, :x, 1)
        @test_throws ArgumentError materialize(ws; normalization=:integer)
        @test materialize(ws; rounding=:nearest).status === :rounded
    end

    # All coefficients must fit even when the common scale would fit.
    tiny = nextfloat(0.0)
    ws = Workspace(fixture([:x, :y], [floatmax(Float64), tiny], zeros(2, 2));
                   integerize_scale=false)
    @test_throws ArgumentError materialize(ws; normalization=:integer)

    # Primitive coefficients are small; the adjusted scale can still overflow,
    # underflow, or lose significant bits. Every such case is rejected.
    for (value, scale) in ((2.0, floatmax(Float64)), (0.5, tiny), (1.5, nextfloat(1.0)))
        ws = Workspace(fixture([:x], [value], zeros(1, 1); scale); integerize_scale=false)
        err = try
            materialize(ws; normalization=:integer)
            nothing
        catch err
            err
        end
        @test err isa ArgumentError
        @test occursin("scale", sprint(showerror, err))
    end
    # The adjacent exact exponent boundaries remain supported.
    for (value, scale, expected) in ((0.5, 2tiny, tiny), (2.0, floatmax(Float64) / 2, floatmax(Float64)))
        ws = Workspace(fixture([:x], [value], zeros(1, 1); scale); integerize_scale=false)
        @test QT.scale(export_model(materialize(ws; normalization=:integer))) == expected
    end

    # A constant-only 54-bit sum cannot hide in an unrepresentable scale.
    ws = Workspace(fixture([:x], [1.0], zeros(1, 1); offset=2.0^-53); integerize_scale=false)
    assume!(ws, :x, 1)
    @test_throws ArgumentError materialize(ws; normalization=:integer)

    # The recorded 9176 constant can be composed from two safe Float64
    # inputs. Normalization makes the stored constant one, but its 66-bit
    # numerator remains unrepresentable in the adjusted scale.
    numerator_9176 = big"62544018350582432251"
    high = ldexp(Float64(numerator_9176 >> 13), -31)
    low = ldexp(Float64(mod(numerator_9176, 8192)), -44)
    @test R(high) + R(low) == numerator_9176 // big(2)^44
    ws = Workspace(fixture([:x], [high], zeros(1, 1); offset=low); integerize_scale=false)
    assume!(ws, :x, 1)
    @test_throws ArgumentError materialize(ws; normalization=:integer)
end
