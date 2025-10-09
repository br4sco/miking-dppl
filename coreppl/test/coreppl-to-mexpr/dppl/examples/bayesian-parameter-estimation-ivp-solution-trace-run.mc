include "bayesian-parameter-estimation-ivp-solution-trace.mc"

mexpr

let true_y_trace = trace true_y (x0, y0) timesExt in

match distEmpiricalSamples #var"Dist_y_trace" with (samples, weights) in
writeFile "bayesian-parameter-estimation-ivp-solution-trace-run.json"
  (jsonObject [
    ("weights", (seqToJson (map floatToJson weights))),
    ("xs", (seqToJson (map floatToJson timesExt))),
    ("trueTrace",
     floatSeqToJson2 (map (lam x : (FloatM, [FloatM]). x.1) true_y_trace)),
    ("trace",
     floatSeqToJson3 (map (map (lam t : (FloatM, [FloatM]). t.1)) samples))
  ])
