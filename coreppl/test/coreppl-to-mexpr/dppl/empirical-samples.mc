let model = lam t : ().
  addf (assume (Gaussian 0. 1.)) (let d = diff negf 1. in d 1.)
mexpr
let dist = infer (Importance { particles = 2 }) model in
utest length (distEmpiricalSamples dist).1 with 2 in
()
