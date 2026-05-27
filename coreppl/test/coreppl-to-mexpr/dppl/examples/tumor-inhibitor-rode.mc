include "../lib.mc"

let solve =
  lam f :
    FloatC -> ModC (ModA ((FloatA, FloatA, FloatA) ->
      (ModC (ModA (FloatA, FloatA, FloatA))))).
    lam xy0 : (FloatC, (FloatA, FloatA, FloatA)).
      lam x1 : FloatC.
        solveode (EFEC {
          add = addt,
          smul = smult,
          stepSize = 1e-4,
          ok =
            lam yh : (FloatP, FloatP, FloatP).
              lam y2h2 : (FloatP, FloatP, FloatP).
                ltf
                  (l2normt (subt yh y2h2))
                  (mulf 3. 1e-2)
        })
          f xy0 x1

let trace =
  lam y : (Float, (FloatA, FloatA, FloatA)) -> ModA (Float ->
    (ModA (FloatA, FloatA, FloatA))).
    lam xy0 : (Float, (Float, Float, Float)).
      lam xs : [Float].
        tail
          (reverse
             (foldl
                (lam xys : [(Float, (FloatA, FloatA, FloatA))]. lam x1 : Float.
                  cons (x1, (y (head xys) x1)) xys)
                [xy0] xs))

let _h = 0.2
let _n = 300
let times = create _n (lam i : Int. mulf _h (int2float (addi i 1)))

-- Parameters
let r = 1.                      -- Cancer cell growth rate
let mu = 0.1                    -- Cancer cell death rate
let nu = 1.
let aP = 4.5                    -- Promotor production rate by cancer cells
let bP = 0.11                   -- Promotor decay rate by cancer cells
let aI = 0.2                    -- Inhibitor production rate by cancer cells
let bI = 0.01                   -- Inhibitor decay rate by cancer cells
let e = 0.34                    -- Cancer cell growth saturation parameter

-- Initial Values
let x0 = 0.

let z0 = 4.
let c0 = 35.
let p0 = mulf (divf aP bP) c0
let i0 = divf (addf z0 (mulf aI c0)) bI

let rode = lam t : ().
  -- Stochastic Process. express inhibitor production from normal tissue.
  let z = lam y : FloatA.
    mulf z0
      (subf 1.
         (mulf
            (mulf 2. nu)
            (mulf y (recipabsf (addf 1. (mulf y y)))))) in


  -- Process noise
  let w = assume (Wiener ()) in

  -- ODE model
  let f = lam aI : FloatA. lam x : FloatC. lam y : (FloatA, FloatA, FloatA).
    match y with (c, p, i)in
    ( subf
        (mulf
           (mulf
              (mulf r c)
              (recipabsf (addf 1. (mulf e c))))
           (mulf p (recipabsf (addf 1. i))))
        (mulf mu c)
    , subf (mulf aP c) (mulf bP p)
    , subf (addf (z (w x)) (mulf aI c)) (mulf bI i) ) in

  -- IVP solution
  let sol =
    lam #var"θ" : FloatA.
      lam xy0 : (Float, (FloatA, FloatA, FloatA)).
        lam x : Float.
          (solve (f #var"θ") xy0 x).1 in

  -- Trace solution and its sensitivity
  let #var"θ" = aI in
  [ trace (sol #var"θ") (x0, (c0, p0, i0)) times
  , diff
      (lam #var"θ" : FloatA. trace (sol #var"θ") (x0, (c0, p0, i0)) times)
      #var"θ"
      1.
  , map (lam t : Float. (t, (w t, 0., 0.))) times
  ]

let #var"Dist_RODE" = infer (Importance { particles = 5 }) rode

mexpr

match distEmpiricalSamples #var"Dist_RODE" with (samples, weights) in
let samples =
  map
    (lam x : [[(Float, (Float, Float, Float))]].
      map
        (lam ts : [(Float, (Float, Float, Float))].
          mapi (lam i : Int. lam t : (Float, (Float, Float, Float)).
            (get times i, [(t.1).0, (t.1).1, (t.1).2]))
            ts)
        x)
    samples in
printWeightedTraces samples weights

-- Local Variables:
-- compile-command: "cppl --seed 1 --cps partial --dppl-typecheck tumor-inhibitor-rode.mc && ./out | dppl-plot-process --lines && rm ./out"
-- End:
