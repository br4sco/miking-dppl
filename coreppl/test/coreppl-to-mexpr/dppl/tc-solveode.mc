mexpr
{

  -- ┌────────────────────┐
  -- │ The time parameter │
  -- └────────────────────┘

  -- TYPE ERROR: We dont allow x to have the type FloatA beacuse the solver
  -- approximates the solution y(x), hence it is not analytic.
  -- a0 =
  --    lam f : FloatA -> FloatA -> FloatA. lam y0 : FloatA. lam x : FloatA.
  --      solveode (Default { add = addf, smul = mulf }) f y0 x,

  a1 =
    lam f : FloatA -> FloatA -> FloatA. lam y0 : FloatA. lam x : Float.
      solveode (Default { add = addf, smul = mulf }) f y0 x,

  a2 =
    lam f : FloatA -> FloatA -> FloatA. lam y0 : FloatA. lam x : FloatN.
      solveode (Default { add = addf, smul = mulf }) f y0 x,

  -- ┌─────────────────────────────┐
  -- │ The initial value parameter │
  -- └─────────────────────────────┘

  -- TYPE ERROR
  -- b0 =
  --   lam f : FloatA -> Float -> Float. lam y0 : FloatA. lam x : Float.
  --     solveode (Default { add = addf, smul = mulf }) f y0 x,

  b1 =
    lam f : FloatA -> Float -> Float. lam y0 : Float. lam x : Float.
      solveode (Default { add = addf, smul = mulf }) f y0 x,

  b2 =
    lam f : FloatA -> Float -> Float. lam y0 : FloatN. lam x : Float.
      solveode (Default { add = addf, smul = mulf }) f y0 x,

  -- ┌───────────────────────────────────────┐
  -- │ The model and initial value parameter │
  -- └───────────────────────────────────────┘

  c0 =
    lam f : FloatA -> Float -> Float. lam y0 : Float. lam x : Float.
      solveode (Default { add = addf, smul = mulf }) f y0 x,

  c1 =
    lam f : FloatA -> FloatA -> Float. lam y0 : Float. lam x : Float.
      solveode (Default { add = addf, smul = mulf }) f y0 x,

  -- TYPE ERROR: This would otherwise allow an unsafe coerce term
  -- `id = lam z : FloatA. solve (lam FloatA. lam : FloatA. 0.) z 0.` where
  --  `id t` coerces any term `t : FloatA` to `FloatN`.
  -- c2 =
  --   lam f : FloatA -> Float -> FloatN. lam y0 : Float. lam x : Float.
  --     solveode (Default { add = addf, smul = mulf }) f y0 x,

  -- TYPE ERRORS: Non-deterministic functions
  -- c3 =
  --   lam f : FloatA -> FloatA -> Rnd Float. lam y0 : Float. lam x : Float.
  --     solveode (Default { add = addf, smul = mulf }) f y0 x,
  -- c4 =
  --   lam f : FloatA -> Rnd (FloatA -> Float). lam y0 : Float. lam x : Float.
  --     solveode (Default { add = addf, smul = mulf }) f y0 x,

  final = ()

}
