include "bayesian-parameter-estimation-ivp-sensitivity-trace.mc"

mexpr

let #var"true_dy/dθ_trace" =
  diff (lam #var"true_θ" : FloatA. trace (y #var"true_θ") (x0, y0) timesExt)
    #var"true_θ" 1. in

match distEmpiricalSamples #var"Dist_dy/dθ_trace" with (samples, weights) in
writeFile "bayesian-parameter-estimation-ivp-sensitivity-trace-run.json"
  (jsonObject [
    ("weights", (seqToJson (map floatToJson weights))),
    ("xs", (seqToJson (map floatToJson timesExt))),
    ("trueTrace",
     floatSeqToJson2 (map (lam x : (FloatM, [FloatM]). x.1) #var"true_dy/dθ_trace")),
    ("trace",
     floatSeqToJson3 (map (map (lam t : (FloatM, [FloatM]). t.1)) samples))
  ])
