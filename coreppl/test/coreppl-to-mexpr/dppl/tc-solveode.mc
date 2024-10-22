let add = lam a : (FloatA, FloatA). lam b : (FloatA, FloatA).
  (addf a.0 b.0, addf a.1 b.1)

let smul = lam s : FloatA. lam a : (FloatA, FloatA).
  (mulf s a.0, mulf s a.1)

mexpr
{

  -- ┌────────────────────┐
  -- │ The time parameter │
  -- └────────────────────┘

  -- TYPE ERROR: We dont allow x to have the type FloatA beacuse the solver
  -- approximates the solution y(x), hence it is not analytic.
  -- a0 =
  --    lam f : FloatA -> FloatA -> FloatA. lam y0 : FloatA. lam x : FloatA.
  --      solveode (Default {}) f y0 x,

  a1 =
    lam f : FloatA -> FloatA -> FloatA. lam y0 : FloatA. lam x : Float.
      solveode (Default {}) f y0 x,

  a2 =
    lam f : FloatA -> FloatA -> FloatA. lam y0 : FloatA. lam x : FloatN.
      solveode (Default {}) f y0 x,

  -- ┌─────────────────────────────┐
  -- │ The initial value parameter │
  -- └─────────────────────────────┘

  -- TYPE ERROR
  -- b0 =
  --   lam f : FloatA -> Float -> Float. lam y0 : FloatA. lam x : Float.
  --     solveode (Default {}) f y0 x,

  b1 =
    lam f : FloatA -> Float -> Float. lam y0 : Float. lam x : Float.
      solveode (Default {}) f y0 x,

  b2 =
    lam f : FloatA -> Float -> Float. lam y0 : FloatN. lam x : Float.
      solveode (Default {}) f y0 x,

  -- ┌───────────────────────────────────────┐
  -- │ The model and initial value parameter │
  -- └───────────────────────────────────────┘

  c0 =
    lam f : FloatA -> Float -> Float. lam y0 : Float. lam x : Float.
      solveode (Default {}) f y0 x,

  c1 =
    lam f : FloatA -> FloatA -> Float. lam y0 : Float. lam x : Float.
      solveode (Default {}) f y0 x,

  -- TYPE ERROR: This would otherwise allow an unsafe coerce term
  -- `id = lam z : FloatA. solve (lam FloatA. lam : FloatA. 0.) z 0.` where
  --  `id t` coerces any term `t : FloatA` to `FloatN`.
  -- c2 =
  --   lam f : FloatA -> Float -> FloatN. lam y0 : Float. lam x : Float.
  --     solveode (Default {}) f y0 x,

  -- TYPE ERRORS: Non-deterministic functions
  -- c3 =
  --   lam f : FloatA -> FloatA -> Rnd Float. lam y0 : Float. lam x : Float.
  --     solveode (Default {}) f y0 x,
  -- c4 =
  --   lam f : FloatA -> Rnd (FloatA -> Float). lam y0 : Float. lam x : Float.
  --     solveode (Default {}) f y0 x,

  -- ┌───────────────┐
  -- │ Vector states │
  -- └───────────────┘

  d0 =
    lam f : FloatA -> (FloatA, FloatA) -> (FloatA, FloatA).
      lam x : FloatN.
        lam g : (FloatA, FloatA) -> FloatA.
          lam h : FloatN -> FloatN.
            h (g ((solveode (Default { add = add, smul = smul }) f (0., 0.) x))),

  -- TYPE ERROR
  -- d1 =
  --   lam f : FloatA -> (FloatA, FloatA) -> (FloatA, FloatA).
  --     lam x : Float.
  --       lam g : (FloatA, FloatA) -> FloatA.
  --         lam h : FloatN -> FloatN.
  --           h (g ((solveode (Default { add = add, smul = smul }) f (0., 0.) x))),

  final = ()

}
