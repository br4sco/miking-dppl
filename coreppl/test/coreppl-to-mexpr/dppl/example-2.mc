include "./lotka-model.mc"

let add = lam a : (Float, Float). lam b : (Float, Float).
  (addf a.0 b.0, addf a.1 b.1)

let smul = lam s : Float. lam a : (Float, Float). (mulf s a.0, mulf s a.1)

-- Number of time-steps
let n = 12
-- Size time-step
let dx = 0.1
-- Time-steps
let xs = create n (lam i : Int. mulf (int2float i) dx)

-- ODE model
let ode =
  lam p : FloatA.
    lam x : Float.
      lam y : (FloatN, FloatA).
        lotkaVolterra (p, 1., 1., 3.) y

-- We can only observe the preys in our model
let output = lam y : (FloatN, FloatA). y.0

-- Initial values
let init = (1., 1.)

-- True parametere value
let p = 1.5

-- Measurement noise
let sigma = 0.2

-- The system is the output trace with the true parameter with added measurement
-- noise.
let system = lam t : ().
  map
    (lam o : Float. let v = assume (Gaussian 0. sigma) in addf o v)
    (map (lam x : Float.
      output (solveode (RK4 { stepSize = 1e-3, add = add, smul = smul })
                (ode p) init x))
       xs)

-- Genereate new data by drawing one sample from the system. The following data
-- use sigma = 0.2.
let data = mapi (lam i : Int. lam o : Float. (get xs i, o)) [
  1.08031492294,
  1.12318304667,
  0.847496932043,
  1.14050788877,
  1.35222496823,
  1.53745426155,
  2.17130541567,
  1.95313820393,
  1.9547110161,
  2.26029735801,
  2.96786845262,
  3.3291466847
]

let model = lam t : ().
  let theta = assume (Gaussian 1. 1.) in
  let sigma = assume (Beta 2. 2.) in
  iter
    (lam t : (Float, Float).
      match t with (x, o) in
      let y =
        solveode (RK4 { stepSize = 1e-3, add = add, smul = smul })
          (ode p) init x
      in
      observe o (Gaussian (output y) sigma))
    data;
  theta

mexpr
let d = infer (APF { particles = 1000 }) model in
print (float2string (expectation d))
