# Bounded numeric-path/export/verification probe; no wall-time acceptance threshold.
using QUBOPreprocessing
import QUBOTools as QT

function proof_case(near)
    model = near ? QT.Model(Dict(:x=>nextfloat(1.0),:y=>0.0,:z=>0.0),
                           Dict((:x,:y)=>1.0,(:x,:z)=>-1.0)) :
                   QT.Model(Dict(:x=>10.0,:y=>0.0,:z=>0.0),
                           Dict((:x,:y)=>1.0,(:x,:z)=>-1.0))
    ws = Workspace(model)
    i = QT.index(model,:x)
    for _ in 1:10; QUBOPreprocessing._dominance_witness(ws,i); end
    bound = @timed for _ in 1:1000; QUBOPreprocessing._dominance_witness(ws,i); end
    prove_dominance(ws,:x)
    capture = @timed prove_dominance(ws,:x)
    attempt = capture.value
    @assert attempt.stop_reason == :proved
    @assert attempt.method == (near ? :exact : :interval)
    verify_certificate(ws,attempt.certificate)
    verification = @timed verify_certificate(ws,attempt.certificate)
    @assert verification.value.valid
    return (; near,method=attempt.method,edge_visits=attempt.edge_visits,
            exact_fallbacks=attempt.exact_fallbacks,exact_work=attempt.exact_work,
            numeric_seconds_per_call=bound.time/1000,numeric_bytes_per_call=bound.bytes/1000,
            proof_export_seconds=capture.time,proof_export_bytes=capture.bytes,
            verifier_seconds=verification.time,verifier_bytes=verification.bytes)
end

proof_case(false); proof_case(true)
println("Julia ",VERSION,"; QUBOTools ",pkgversion(QT),"; numeric repetitions=1000; threads=1 recommended")
println(proof_case(false))
println(proof_case(true))
