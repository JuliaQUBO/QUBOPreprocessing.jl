# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

@testset "explicit recorded residual rounding" begin
    R = Rational{BigInt}
    # Independent substitution: fixing x=1 adds 2^-53 to y's field and
    # 2^-54 to the constant; both input terms are individually exact Float64s.
    for scale in (-3.0, 0.0, 2.5)
        m = fixture([:x, :y], [1.0, 1.0], [0.0 2.0^-53; 0.0 0.0];
                    scale, offset=2.0^-54)
        ws = Workspace(m; integerize_scale=false)
        assume!(ws, :x, 1)
        err = try
            materialize(ws)
            nothing
        catch err
            err
        end
        @test err isa ArgumentError
        message = sprint(showerror, err)
        @test occursin("linear coefficient for variable :y", message)
        @test occursin("54 significant numerator bits", message)
        @test occursin("CallerAssumption", message)
        @test occursin("cannot attribute", message)
        @test occursin("coefficient_type=Rational{BigInt}", message)
        @test occursin("rounding=:nearest", message)
        @test occursin("integerize_scale", message)

        rounded = materialize(ws; rounding=:nearest)
        model = export_model(rounded)
        expected_linear = R(1) + R(2.0^-53)
        expected_constant = R(1) + R(2.0^-54)
        expected_error = abs(R(scale)) * max(
            abs(R(linear(model)[1]) - expected_linear),
            abs(R(QT.offset(model)) - expected_constant))
        @test rounded.status === :rounded
        @test !rounded.certificate.unchanged_representation
        @test rounded.max_perturbation == expected_error
        @test rounded.perturbed == !iszero(expected_error)
        @test linear(model)[1] == 1.0
        @test QT.offset(model) == 1.0
        @test QT.scale(model) == scale
        @test !ws.perturbed && iszero(ws.max_perturbation)
        exact = export_model(materialize(ws; coefficient_type=R))
        @test linear(exact)[1] == expected_linear
        @test QT.offset(exact) == expected_constant
        @test reconstruct(rounded, [1]).state == [1, 1]
        @test reconstruct(rounded, [1]).energy.value ==
            reference([1.0, 1.0], [0.0 2.0^-53; 0.0 0.0], scale, 2.0^-54, [1, 1])
        # Source mutation, later workspace edits, and independently exported
        # models cannot alter the retained historical export.
        cp = checkpoint(ws)
        assume!(ws, :y, 0)
        @test reconstruct(rounded, [1]).state == [1, 1]
        rollback!(ws, cp)
        @test deepcopy(rounded).max_perturbation == expected_error
    end

    # The certificate remains exact and verifiable even though the solver
    # export additionally records a residual-rounding perturbation.
    ws = Workspace(fixture([:x, :y], [-2.0, 1.0], [0.0 2.0^-53; 0.0 0.0]); rules=:dominance)
    @test apply_dominance!(ws, :x).stop_reason === :applied
    rounded = materialize(ws; rounding=:nearest)
    @test rounded.status === :rounded
    @test rounded.perturbed
    @test !rounded.certificate.proof.perturbed
    @test iszero(rounded.certificate.proof.max_perturbation)
    @test verify_certificate(ws, rounded.certificate.proof).valid
    @test reconstruct(rounded, [0]).state == [1, 0]

    # A relation creates an inexact coupling by adding two original edges.
    ws = Workspace(fixture([:x, :y, :z], zeros(3),
        [0.0 -4.0 1.0; 0.0 0.0 2.0^-53; 0.0 0.0 0.0]; domain=:spin);
        rules=:relations, integerize_scale=false)
    @test contract_relation!(ws, :x, :y; sign=1).stop_reason === :applied
    err = try
        materialize(ws)
        nothing
    catch err
        err
    end
    @test err isa ArgumentError
    @test occursin("coupling (:y, :z)", sprint(showerror, err))
    @test occursin("RelationStep", sprint(showerror, err))
    rounded = materialize(ws; rounding=:nearest)
    @test quadratic(export_model(rounded))[1, 2] == 1.0
    @test rounded.max_perturbation == R(2.0^-53)
    @test verify_certificate(ws, rounded.certificate.proof).valid

    # Constant-only residuals need the same accounting and useful diagnosis.
    ws = Workspace(fixture([:x], [1.0], zeros(1, 1); offset=2.0^-53))
    assume!(ws, :x, 1)
    err = try
        materialize(ws)
        nothing
    catch err
        err
    end
    @test occursin("conditioned constant", sprint(showerror, err))
    rounded = materialize(ws; rounding=:nearest)
    @test QT.dimension(export_model(rounded)) == 0
    @test rounded.max_perturbation == R(2.0^-53)
    @test reconstruct(rounded, Int[]).state == [1]

    # Mapping can introduce underflow in all coefficient families. The exact
    # binary-value comparison also covers the positional map forwarding API.
    tiny = nextfloat(0.0)
    ws = Workspace(fixture([:x, :y], zeros(2), [0.0 tiny; 0.0 0.0]); integerize_scale=false)
    dmap = domain_map(ws; domain=:spin)
    exact = export_model(materialize(ws, dmap; coefficient_type=R))
    rounded = materialize(ws, dmap; rounding=:nearest)
    model = export_model(rounded)
    @test rounded.status === :rounded
    @test rounded.max_perturbation == R(tiny) / 4
    @test R(quadratic(exact)[1, 2]) - R(quadratic(model)[1, 2]) == rounded.max_perturbation
    @test reconstruct(rounded, [-1, 1]).state == [0, 1]

    # Input perturbation and export rounding use the same effective units;
    # retaining their maximum does not claim an end-to-end objective bound.
    m = fixture([:x, :y, :z], [0.1, 0.1, 2.0^49],
        [0.0 0.0 2.0^49; 0.0 0.0 0.1; 0.0 0.0 0.0])
    ws = Workspace(m; integerize_scale=true, max_decimals=1, atol=1e-12)
    assume!(ws, :x, 1)
    assume!(ws, :y, 1)
    @test ws.perturbed
    rounded = materialize(ws; rounding=:nearest)
    exact = export_model(materialize(ws; coefficient_type=R))
    model = export_model(rounded)
    residual_error = abs(R(QT.scale(exact))) * max(
        abs(R(linear(model)[1]) - linear(exact)[1]),
        abs(R(QT.offset(model)) - QT.offset(exact)))
    @test rounded.status === :rounded
    @test residual_error > 0
    @test rounded.max_perturbation == max(ws.max_perturbation, residual_error)

    identity_ws = Workspace(fixture([:x], [1.0], zeros(1, 1)))
    identity_export = materialize(identity_ws; rounding=:nearest)
    @test identity_export.status === :certified
    @test !identity_export.perturbed
    @test identity_export.certificate.unchanged_representation
    @test_throws ArgumentError materialize(identity_ws; rounding=:up)
    @test_throws ArgumentError materialize(identity_ws; coefficient_type=R, rounding=:nearest)
    @test_throws ArgumentError materialize(ws; rounding=:up)

    # Nearest rounding never silently exports an infinite coefficient.
    ws = Workspace(fixture([:x], [floatmax(Float64)], zeros(1, 1); offset=floatmax(Float64)))
    assume!(ws, :x, 1)
    @test_throws ArgumentError materialize(ws; rounding=:nearest)
end
