mexpr
{
  a0 = infer (Importance { particles = 1 })
         (lam t : ().
           weight 0.;
           observe 1. (Uniform 1. 1.);
           assume (Uniform 1. 1.)),

  a1 = expectation (Uniform 1. 1.),

  final = ()

}; ()
