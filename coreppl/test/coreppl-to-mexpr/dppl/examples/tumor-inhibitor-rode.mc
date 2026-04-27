include "../lib.mc"

let solve =
  lam f : FloatC -> ModC ((FloatA, (FloatA, FloatA, FloatA)) -> (FloatA, (FloatA, FloatA, FloatA))).
    lam xy0 : (FloatC, (FloatA, (FloatA, FloatA, FloatA))).
      lam x1 : FloatC.
        solveode (EFEC {
          add =
            lam a : (FloatA, (FloatA, FloatA, FloatA)).
              lam b : (FloatA, (FloatA, FloatA, FloatA)).
                (addf a.0 b.0, addt a.1 b.1),
          smul = lam a : FloatA. lam b : (FloatA, (FloatA, FloatA, FloatA)).
            (mulf a b.0, smult a b.1),
          stepSize = 1e-4,
          ok =
            lam yh : (FloatP, (FloatP, FloatP, FloatP)).
              lam y2h2 : (FloatP, (FloatP, FloatP, FloatP)).
                ltf
                  (l2normt (subt yh.1 y2h2.1))
                  (mulf 3. 1e-2)
        })
          f xy0 x1

let trace =
  lam y : (FloatC, (FloatA, FloatA, FloatA)) -> FloatC -> (FloatA, (FloatA, FloatA, FloatA)).
    lam xy0 : (FloatC, (FloatA, FloatA, FloatA)).
      lam xs : [FloatC].
        tail
          (reverse
             (foldl
                (lam xys : [(FloatC, (FloatA, FloatA, FloatA))]. lam x1 : FloatC.
                  cons (y (head xys) x1) xys)
                [xy0] xs))

let diff1 = lam f : FloatA -> ModP ([(FloatA, (FloatA, FloatA, FloatA))]). lam x : FloatA.
  diff f x 1.

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

let recip1 = lam x : FloatA.
  divf 1. (addf 1. (addf x (exp (subf (mulf (negf 100.) x) 100.))))

let recipabs = lam x : FloatA.
  divf 1. (sqrt (addf (mulf x x) (mulf 0.01 0.01)))

let rode = lam t : ().
  -- Stochastic Process. express inhibitor production from normal tissue.
  -- let z = lam y : FloatA.
  --   mulf z0
  --     (subf 1.
  --        (mulf
  --           (mulf 2. nu)
  --           (mulf y (recip1 (mulf y y))))) in

  let z = lam y : FloatA.
    mulf z0
      (subf 1.
         (mulf
            (mulf 2. nu)
            (mulf y (recipabs (addf 1. (mulf y y)))))) in


  -- Process noise
  let w = assume (Wiener ()) in

  -- ODE model
  -- let f = lam x : FloatC. lam y : (FloatA, (FloatA, FloatA, FloatA)).
  --   match y with (e, (c, p, i)) in
  --   ( 0.
  --   , ( subf
  --         (mulf
  --            (mulf
  --               (mulf r c)
  --               (recip1 (mulf e c)))
  --            (mulf p (recip1 i)))
  --         (mulf mu c)
  --     , subf (mulf aP c) (mulf bP p)
  --     , subf (addf (z (w x)) (mulf aI c)) (mulf bI i) )) in
  let f = lam x : FloatC. lam y : (FloatA, (FloatA, FloatA, FloatA)).
    match y with (aI, (c, p, i)) in
    ( 0.
    , ( subf
          (mulf
             (mulf
                (mulf r c)
                (recipabs (addf 1. (mulf e c))))
             (mulf p (recipabs (addf 1. i))))
          (mulf mu c)
      , subf (mulf aP c) (mulf bP p)
      , subf (addf (z (w x)) (mulf aI c)) (mulf bI i) )) in


  -- IVP solution
  let y =
    lam #var"θ" : FloatA.
      lam xy0 : (FloatC, (FloatA, FloatA, FloatA)).
        lam x : FloatC.
          match xy0 with (x0, y0) in
          match solve f (x0, (#var"θ", y0)) x with (x1, (_, y1)) in
          (x1, y1) in

  -- Trace solution and its sensitivity
  let #var"θ" = aI in
  [
    trace (y #var"θ") (x0, (c0, p0, i0)) times,
    diff1 (lam #var"θ" : FloatA. trace (y #var"θ") (x0, (c0, p0, i0)) times) #var"θ",
    map (lam t : FloatC. (t, (w t, 0., 0.))) times
  ]

let #var"Dist_RODE" = infer (Importance { particles = 5 }) rode

mexpr

match distEmpiricalSamples #var"Dist_RODE" with (samples, weights) in
let samples =
  map
    (map
       (mapi (lam i : Int. lam t : (FloatM, (FloatM, FloatM, FloatM)).
         (get times i, [(t.1).0, (t.1).1, (t.1).2]))))
    samples in
printWeightedTraces samples weights


-- Local Variables:
-- compile-command: "cppl --seed 1 --cps partial --dppl-typecheck tumor-inhibitor-rode.mc && ./out | dppl-plot-process --lines && rm ./out"
-- End:
