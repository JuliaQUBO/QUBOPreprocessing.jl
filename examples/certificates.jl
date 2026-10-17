using QUBOPreprocessing
import QUBOTools as QT

ws = Workspace(QT.Model(Dict(:x=>3.0,:y=>0.0),Dict((:x,:y)=>-1.0)))
attempt = prove_dominance(ws,:x;max_work=2,max_exact_work=0)
@assert attempt.stop_reason == :proved
@assert attempt.method == :interval
@assert verify_certificate(ws,attempt.certificate).valid
@assert only(attempt.certificate.steps).value == 0
@assert isempty(assumptions(ws)) # proving is read-only; propagation is a separate mutating call

conditional = Workspace(QT.Model(Dict(:x=>1.0,:y=>0.0),Dict((:x,:y)=>-2.0)))
root = checkpoint(conditional)
@assert prove_dominance(conditional,:x).certificate === nothing
assume!(conditional,:y,0)
proof = prove_dominance(conditional,:x).certificate
@assert verify_certificate(conditional,proof).valid
rollback!(conditional,root)
@assert !verify_certificate(conditional,proof).valid
