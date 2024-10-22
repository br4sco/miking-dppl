mexpr
(
  -- Analytic modifier on the float type
  lam x : FloatA. x,

  -- No modifier corresponds to the P (PAP) modifier in the formalization. Which
  -- essentially means that the functions with parameters of this type are
  -- differentiable in the AD sense.
  lam x : Float. x,

  -- Non differential modifier on the float type
  lam x : FloatN. x,

  -- A normal arrow corresponds to a deterministic function (Det modifier in the
  -- formalization).
  lam f : FloatA -> FloatA. f,

  -- The Rnd modifier denotes a random computation.
  lam f : FloatA -> Rnd FloatA. f,

  -- We need to group it if we have curried functions.
  lam f : FloatA -> Rnd (FloatA -> Rnd FloatA). f
)
