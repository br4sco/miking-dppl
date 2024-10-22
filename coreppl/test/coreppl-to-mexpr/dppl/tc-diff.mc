mexpr
{
  a0 = lam f : FloatA -> Float. lam x : Float. diff f x,

  a1 = lam f : Float -> Float. lam x : Float. diff f x,

  -- TYPE ERROR: Trying to differentiate a non-differential function.
  -- a2 = lam f : FloatN -> Float. lam x : FloatN. diff f x,

  -- TYPE ERROR: Non-deterministic function
  -- a3 = lam f : Float -> Rnd Float. lam x : Float. diff f x,

  final = ()
}; ()
