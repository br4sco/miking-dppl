include "tuple.mc"
include "math.mc"

recursive let _repeat = lam f. lam n. lam acc.
  if leqi n 0 then acc
  else _repeat f (subi n 1) (f acc)
end

let _checkStepSize = lam h.
  if ltf h 0. then
    error "odeSolver: non positive step-size"
  else ()

let _solveFixedH
  : all a. (a -> Float -> Float -> a) -> (Float, a) -> Float -> Float -> (Float, a)
  = lam step. lam tx0. lam h. lam t1.
    match tx0 with (t0, x0) in
    let sgn = if leqf t0 t1 then 1. else -1. in
    let h = mulf sgn h in
    recursive let recur = lam t. lam x.
      if leqf (mulf sgn (subf t1 (addf t h))) 0. then
        let h = subf t1 t in
        (addf t h, step x t h)
      else
        recur (addf t h) (step x t h)
    in recur t0 x0

let _solveFixed
  : all a. (a -> Float -> Float -> a) -> (Float, a) -> Float -> Float -> (Float, a)
  = lam step. lam tx0. lam h. lam t1.
    if eqf tx0.0 t1 then tx0 else _solveFixedH step tx0 h t1

-- ┌───────────────┐
-- │ Euler-Forward │
-- └───────────────┘

-- `add`  : Implements vector addition
-- `smul` : Implements scalar multiplication
-- `h`    : Step-size of the integration
-- `f`    : Right-hand side in x'(t) = f(t, x(t))
-- `tx0`  : Initial value (t0, x(t0))
-- `t1`   : Final time
-- returns the solution x(t1) at the time t1 and t1
let odeSolverEFSolve
  : all a. (a -> a -> a) -> (Float -> a -> a) -> Float ->
      (Float -> a -> a) -> (Float, a) -> Float -> (Float, a)
  = lam add. lam smul. lam h.
    lam f. lam tx0. lam t1.
      _checkStepSize h;
      let integrate = lam x. lam t. lam h. add x (smul h (f t x)) in
      _solveFixed integrate tx0 h t1

-- ┌────────────────────────┐
-- │ Euler-Forward Averaged │
-- └────────────────────────┘

-- `add`  : Implements vector addition
-- `smul` : Implements scalar multiplication
-- `h`    : Step-size of the integration
-- `n`    : The number if intervals to split `h` when averaging over t
-- `f`    : Right-hand side in x'(t) = f(t, x(t))
-- `tx0`  : Initial value (t0, x(t0))
-- `t1`   : Final time
-- returns the solution x(t1) at the time t1 and t1
let odeSolverEFASolve
  : all a. (a -> a -> a) -> (Float -> a -> a) -> Float -> Int ->
    (Float -> a -> a) -> (a, Float) -> (Float, a)
  = lam add. lam smul. lam h. lam n.
    lam f. lam tx0. lam t1.
      _checkStepSize h;
      let dt = divf h (int2float n) in
      let integrate =
        lam x. lam t. lam h.
          let f =
            _repeat
              (lam acc.
                match acc with (t, sum) in
                let t = addf t dt in
                (t, add sum (smul h (f t x))))
              (subi n 1)
              (t, smul h (f t x)) in
          add x (smul (divf 1. (int2float n)) f.1) in
      _solveFixed integrate tx0 h t1

-- ┌──────────────────────────┐
-- │ Runge-Kutta Fourth Order │
-- └──────────────────────────┘

-- ** INTEGRATION STEP FUNCTION
-- Fourth order explicit Runge Kutta (RK4) ODEs integration step.
-- `add`  : Implements vector addition
-- `smul` : Implements scalar multiplication
-- `f`    : Right-hand side in x'(t) = f(t, x(t))
-- `x`    : x(t)
-- `t`    : Time
-- `h`    : Step-size of the integration
-- returns x(t+h)
let odeSolverRK4Integrate
  : all a. (a -> a -> a) -> (Float -> a -> a) -> (Float -> a -> a) -> a -> Float -> Float -> a
  = lam add. lam smul. lam f. lam x. lam t. lam h.
    let h2 = divf h 2. in
    let t2 = addf t h2 in
    let th = addf t h in
    let k1s = f t x in
    let x1 = add x (smul h2 k1s) in
    let k2s = f t2 x1 in
    let x2 = add x (smul h2 k2s) in
    let k3s = f t2 x2 in
    let x3 = add x (smul h k3s) in
    let k4s = f th x3 in
    add
      x
      (smul
         (divf h 6.)
         (add
            k1s
            (add
               (smul 2. k2s)
               (add (smul 2. k3s) k4s))))

-- Fourth order explicit Runge Kutta (RK4) ODEs solver.
-- `add`  : Implements vector addition
-- `smul` : Implements scalar multiplication
-- `h`    : Step-size of the integration
-- `f`    : Right-hand side in x'(t) = f(t, x(t))
-- `tx0`  : Initial value (t0, x(t0))
-- `t1`   : Final time
-- returns the solution x(t1) at the time t1 and t1
let odeSolverRK4Solve
  : all a. (a -> a -> a) -> (Float -> a -> a) -> Float ->
    (Float -> a -> a) -> (Float, a) -> Float -> (Float, a)
  = lam add. lam smul. lam h.
    lam f. lam tx0. lam t1.
      _checkStepSize h;
      _solveFixed (odeSolverRK4Integrate add smul f) tx0 h t1

mexpr

let eq2 = lam eq. tupleEq2 eq eq in

-- Harmonic oscillator
let f = lam t. lam x. (x.1, (negf x.0)) in

-- Analytic solution
let x = lam t. (t, (sin t, cos t)) in

let opt = {
  stepSize = 1e-5,
  add = lam a. lam b. (addf a.0 b.0, addf a.1 b.1),
  smul = lam s. lam a. (mulf s a.0, mulf s a.1) } in

-- ┌───────────────────────────┐
-- │ Test Euler Forward Solver │
-- └───────────────────────────┘

let eq = tupleEq2 (eqfApprox 1e-16) (eq2 (eqfApprox 1e-4)) in

let xHat = odeSolverEFSolve opt.add opt.smul opt.stepSize f (x -1.) in
utest xHat 1. with x 1. using eq in
utest xHat 2. with x 2. using eq in
utest xHat 3. with x 3. using eq in

let xHat = odeSolverEFSolve opt.add opt.smul opt.stepSize f (x 1.) in
utest xHat -1. with x -1. using eq in
utest xHat -2. with x -2. using eq in
utest xHat -3. with x -3. using eq in

-- ┌──────────────────────────────────────┐
-- │ Test Runge-Kutta Fourth Order Solver │
-- └──────────────────────────────────────┘

let eq = tupleEq2 (eqfApprox 1e-16) (eq2 (eqfApprox 1e-7)) in

let xHat = odeSolverRK4Solve opt.add opt.smul opt.stepSize f (x -1.) in
utest xHat 1. with x 1. using eq in
utest xHat 2. with x 2. using eq in
utest xHat 3. with x 3. using eq in

let xHat = odeSolverRK4Solve opt.add opt.smul opt.stepSize f (x 1.) in
utest xHat -1. with x -1. using eq in
utest xHat -2. with x -2. using eq in
utest xHat -3. with x -3. using eq in

()
