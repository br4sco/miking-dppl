/-

  Extended testing of new DPPL type-checker and its parser additions

 -/

include "result.mc"
include "either.mc"
include "./dppl-type-check.mc"
include "./parser.mc"

lang TestLang = DTCTypeOf + MExprPPL + DPPLParser end

mexpr

use TestLang in

let _D = ModD () in
let _R = ModR () in
let _A = ModA () in
let _P = ModP () in
let _C = ModC () in
let _M = ModM () in

let arrce = lam ps. lam ret. foldr (lam t. lam to. tyarrowce_ t.0 to t.1 t.2) ret ps in
let arrc = lam ps. arrce (map (lam p. (p.0, p.1, _D)) ps) in
let arre = lam ps. arrce (map (lam p. (p.0, _A, p.1)) ps) in
let arr = lam ps. arrce (map (lam p. (p, _A, _D)) ps) in
let flt = tyfloatc_ in

let _typeOf = lam env. lam prog.
  (result.consume
     (typeOf (dtcEnvOfSeq env)
        (decorateTypesExn
           (symbolizeAllowFree (parseMExprPPLString prog))))).1 in

let fi = lam row1. lam col1. lam row2. lam col2.
  Info { filename = "", row1 = row1, col1 = col1, row2 = row2, col2 = col2 } in

let eq =
  eitherEq
    (lam l. lam r.
      forAll (lam x. x)
        (zipWith (lam l. lam r.
          and
            ( switch (typeErrorInfo l, typeErrorInfo r)
              case (Info l, Info r) then
              let seq = lam r. [r.row1, r.row2, r.col1, r.col2] in
              let eq = lam l. lam r. allb (zipWith eqi (seq l) (seq r)) in
              eq l r
              case (NoInfo _, NoInfo _) then true
              case _ then false
              end )
            (eqi (constructorTag l) (constructorTag r)))
           l r))
    (tupleEq2 dtcEqe eqType)
in

let toString =
  eitherEither
    (lam errs.
      strJoin "\n"
        (map (lam err. match typeErrorToMsg err with (info, msg) in
                     strJoin "\n" [msg, info2str (typeErrorInfo err)])
           errs))
    (lam t. join [":", dtcEffectToString t.0, " ", type2str t.1])
in
let onFail = utestDefaultToString toString toString in

let env = [] in
utest _typeOf env (strJoin "\n" [
  "let a : ModA Float = 0. in",
  "let b : ModP Float = 0. in",
  "let c : ModC Float = 0. in",
  "let d : ModM Float = 0. in",
  "(a, b, c, d)" ])
  with Right (_D, tytuple_ (map flt [_M, _M, _M, _M]) )
  using eq else onFail in

let env = [] in
utest _typeOf env (strJoin "\n" [
  "(lam a : ModA Float. (lam b : ModM Float. (a, b)) 0.) 0." ])
  with Right (_D, tytuple_ (map flt [_M, _M]) )
  using eq else onFail in

let env = [
  (nameNoSym "test", arr [tytuple_ (map flt [_A, _P, _C, _M])] tyunit_)
] in
utest _typeOf env (strJoin "\n" [
  "let a : ModA Float = 0. in",
  "let b : ModP Float = 0. in",
  "let c : ModC Float = 0. in",
  "let d : ModM Float = 0. in",
  "test (a, b, c, d)" ])
  with Right (_D, tyunit_ )
  using eq else onFail in

let env = [
  (nameNoSym "test", arr [tytuple_ (map flt [_M, _C, _P, _A])] tyunit_)
] in
utest _typeOf env (strJoin "\n" [
  "let a : ModA Float = 0. in",
  "let b : ModP Float = 0. in",
  "let c : ModC Float = 0. in",
  "let d : ModM Float = 0. in",
  "test (a, b, c, d)" ])
  with Left [DTCArgError (fi 5 5 5 17, None ())]
  using eq else onFail in

let env = [
  (nameNoSym "f", arrc [(tytuple_ [(flt _M), (flt _M)], _M)] (flt _A)),
  (nameNoSym "data", tyseq_ (tytuple_ [(flt _M), (flt _M)]))
] in
utest _typeOf env (strJoin "\n" [
  "let regressionModel =",
  "  lam f : (ModM Float, ModM Float) -> ModM (ModR Float).",
  "  lam d : [(ModM Float, ModM Float)].",
  "  lam t : ().",
  "    match (assume (Gaussian 1. 1.), assume (Beta 2. 2.))",
  "    with (theta, nu) in",
  "    iter",
  "      (lam t : (ModM Float, ModM Float).",
  "         match t with (x, y) in observe y (Gaussian (f (x, theta)) nu)) d;",
  "      theta in",
  "infer (Default ()) (regressionModel f data)" ])
  with Right (_D, tydist_ (flt _M) )
  using eq else onFail in

let env = [
  (nameNoSym "r", flt _M)       -- represents arbritrary float literal which we
                                -- can type with any coeffect modifier.
] in
utest _typeOf env (strJoin "\n" [
  "let y = lam x : ModA Float. addf (mulf x x) x in",
  "diff y r 1." ])
  with Right (_D, flt _M)
  using eq else onFail in

let env = [] in
utest _typeOf env "lam x : ModA Float. if ltf x 0. then x else subf 0. x"
  with Left [DTCArgError (fi 1 27 1 28, None ())]
  using eq else onFail in

let env = [
  (nameNoSym "r", flt _M)
] in
utest _typeOf env (strJoin "\n" [
  "let y = lam x : ModP Float. if ltf x 0. then x else subf 0. x in",
  "diff y r 1." ])
  with Right (_D, flt _M)
  using eq else onFail in

let env = [
  (nameNoSym "t", tydist_ (flt _A)),
  (nameNoSym "r", flt _M)
] in
utest _typeOf env (strJoin "\n" [
  "let y = assume t in",
  "diff (lam x : ModA Float. x) r 1." ])
  with Right (_R, flt _M)
  using eq else onFail in

let env = [
  (nameNoSym "r", flt _M)
] in
utest _typeOf env (strJoin "\n" [
  "let w = assume (Wiener ()) in",
  "let z = lam xy: (ModC Float, ModA Float).",
  "  match xy with (x, y) in addf (w x) y in",
  "diff (lam u : ModA Float. z (r, u)) r 1." ])
  with Right (_R, flt _M)
  using eq else onFail in

let env = [
  (nameNoSym "wiener", arrc [(flt _C, _M)] (flt _A)),
  (nameNoSym "x", flt _C),
  (nameNoSym "y", flt _A)
] in
utest _typeOf env "addf (wiener (addf x 1.)) y"
  with Right (_D, flt _A)
  using eq else onFail in

let env = [
  (nameNoSym "wiener", arrc [(flt _C, _M)] (flt _A))
] in
utest _typeOf env (strJoin "\n" [
  "lam y : ModA Float. lam x : ModC Float. ",
  "  addf (wiener (addf x 1.)) y" ])
  with Right (_D, arrc [(flt _A, _M), (flt _C, _A)] (flt _A))
  using eq else onFail in

let env = [
  (nameNoSym "wiener", arrc [(flt _C, _M)] (flt _A))
] in
utest _typeOf env (strJoin "\n" [
  "lam x : ModC Float. lam y : ModA Float. ",
  "  addf (wiener (addf x 1.)) y" ])
  with Right (_D, arrc [(flt _C, _M), (flt _A, _C)] (flt _A))
  using eq else onFail in

let env = [
  (nameNoSym "wiener", arrc [(flt _C, _M)] (flt _A))
] in
utest _typeOf env (strJoin "\n" [
  "lam z : ModA Float. diff (lam y : ModA Float.",
  "  (lam x : (ModC Float, ModA Float). addf (wiener x.0) x.1) (0., y))",
  "  1. z" ])
  with Right (_D, arrc [(flt _A, _M)] (flt _A))
  using eq else onFail in

()
