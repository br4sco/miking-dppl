/- This example programs illustrates Bayesian regression -/

let regressionModel =
   lam d : [FloatM]. lam z : FloatM -> ModM (ModR [Float]). lam t : ().
    match (assume (Gaussian 1. 1.), assume (Gamma 1. 1.))
      with (#var"θ", #var"𝜎²") in
    iter
      (lam t : (FloatM, FloatM).
        match t with (y, z) in observe y (Gaussian z (sqrt #var"𝜎²")))
      (zip (z #var"θ") d);
    #var"θ"
