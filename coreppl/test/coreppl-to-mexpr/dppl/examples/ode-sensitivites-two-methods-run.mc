include "ode-sensitivites-two-methods.mc"

mexpr

match distEmpiricalSamples #var"Dist_dy/dθ" with (samples, weights) in
writeFile "ode-sensitivites-two-methods-run.json"
  (jsonObject [
    ("xs", seqToJson (map floatToJson times)),
    ("samples",
     floatSeqToJson4 (map (map (map (lam t : (FloatM, [FloatM]). t.1))) samples))
  ])
