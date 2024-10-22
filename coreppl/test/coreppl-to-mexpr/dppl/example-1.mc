
-- Analytic scalar derivative
let d = lam f : FloatA -> FloatA. lam x : FloatA. let t = diff f x in t 1.

mexpr
let model = lam t : ().
  let beta = assume (Beta 2. 2.) in
  let theta = assume (Gaussian beta 1.) in
  let f = lam x : FloatA. addf (mulf theta (sin x)) x in
  -- let f = lam x : FloatA. addf (mulf (assume (Gaussian beta 1.)) (sin x)) x in -- Give type error as expected
  observe 2. (Gaussian (d f 1.) 0.1); beta
in
infer (Default {}) model;
()
