/-

  A small library for the examples in this folder.

-/

-- `and a b` is the the logical AND between a and b
let and = lam a : Bool. lam b : Bool. if a then if b then true else false else false

-- `absf x` is the absolute value of x.
let absf = lam x : FloatP. if ltf x 0. then negf x else x

-- `eqfApprox e a b` is true if |a - b| < e.
let eqfApprox = lam e : FloatP. lam a : FloatP. lam b : FloatP. ltf (absf (subf a b)) e

-- zips two sequences of floats
let zip = lam a : [FloatA]. lam b : [FloatA].
  mapi (lam i : Int. lam a : FloatA. (a, get b i)) a

-- `onehots n i` is a seqence of zeros expcept at index `i`, where it is `1.`.
let onehots = lam n : Int. lam i : Int.
  create n (lam j : Int. if eqi i j then 1. else 0.)

-- Vector addition
let adds = lam a : [FloatA]. lam b : [FloatA].
  map (lam t : (FloatA, FloatA). addf t.0 t.1) (zip a b)

-- Vector substraction
let subs = lam a : [FloatA]. lam b : [FloatA].
  map (lam t : (FloatA, FloatA). subf t.0 t.1) (zip a b)

-- Vector L2 norm
let l2norms = lam a : [FloatA].
  foldl addf 0. (map (lam x : FloatA. mulf x x) a)

-- Scalar multiplication
let smuls = lam s : FloatA. map (mulf s)

-- Add pairs
let addp = lam a : (FloatA, FloatA). lam b : (FloatA, FloatA).
  (addf a.0 b.0, addf a.1 b.1)

-- Substract pairs
let subp = lam a : (FloatA, FloatA). lam b : (FloatA, FloatA).
  (subf a.0 b.0, subf a.1 b.1)

-- Pairs L2 norm
let l2normp = lam a : (FloatA, FloatA).
  addf (mulf a.0 a.0) (mulf a.1 a.1)

-- Scalar multiplication of pairs
let smulp = lam s : FloatA. lam a : (FloatA, FloatA).
  (mulf s a.0, mulf s a.1)

-- Vector equality
let eqs = lam a : [FloatP]. lam b : [FloatP].
  foldl and true (map (lam t : (FloatP, FloatP). eqfApprox 0.05 t.0 t.1) (zip a b))

-- pretty prints a float to standard out.
let ppFloat = lam x : FloatM. print (float2string x)

-- pretty prints a sequence of floats to standard out.
let ppFloatSeq = lam xs : [FloatM].
  let n = length xs in
  print "[";
  iteri
    (lam i : Int. lam x : FloatM.
      ppFloat x; (if lti i (subi n 1) then print "," else print "]"))
    xs

-- prints an ode trace, consisting of time-value pairs, to standard out.
let ppODETrace = lam tr : [(FloatM, [FloatM])].
  let ppf = ppFloat in
  let n = length tr in
  print "[";
  iteri
    (lam i : Int. lam p : (FloatM, [FloatM]).
      match p with (t, xs) in
      print "("; ppf t; print ","; ppFloatSeq xs; print ")";
      (if lti i (subi n 1) then print "," else print "]"))
    tr

-- pretty print a sequence of ODE traces
let ppODETraces = lam trs : [[(FloatM, [FloatM])]].
  let n = length trs in
  print "[";
  iteri
    (lam i : Int. lam tr : [(FloatM, [FloatM])].
      ppODETrace tr; (if lti i (subi n 1) then print "," else print "]"))
    trs

-- Prints a distribution of floating point numbers.
let printFloatDist = lam dist : Dist FloatM.
  match distEmpiricalSamples dist with (samples, weights) in
  iteri
    (lam i : Int. lam s : FloatM.
      print (float2string s);
      print " ";
      print (float2string (get weights i));
      print "\n";
      ())
    samples

-- Prints a weighted trace.
let printWeightedTrace = lam samples : [[(FloatM, [FloatM])]]. lam weights : [FloatM].
  iteri
    (lam i : Int. lam s : [(FloatM, [FloatM])].
      ppODETrace s;
      print " ";
      print (float2string (get weights i));
      print "\n";
      ())
    samples

-- Prints a distribution of a trace.
let printTraceDist = lam dist : Dist [(FloatM, [FloatM])].
  match distEmpiricalSamples dist with (samples, weights) in
  printWeightedTrace samples weights

-- Prints weighted traces.
let printWeightedTraces =
  lam samples : [[[(FloatM, [FloatM])]]]. lam weights : [FloatM].
    iteri
      (lam i : Int. lam s : [[(FloatM, [FloatM])]].
        ppODETraces s;
        print " ";
        print (float2string (get weights i));
        print "\n";
        ())
      samples

-- Prints a distribution of traces.
let printTracesDist = lam dist : Dist [[(FloatM, [FloatM])]].
  match distEmpiricalSamples dist with (samples, weights) in
  printWeightedTraces samples weights

-- JSON export helpers
let strJoin = lam del : String. lam strs : [String].
  switch strs
  case [] then ""
  case [hd] ++ tl then
    foldl (lam acc : String. lam el : String. concat acc (concat del el)) hd tl
  end

let floatToJson = lam r : FloatM.
  if eqf r r then
    if eqf r (divf 1. 0.) then "Infinity"
    else
      if eqf r (divf -1. 0.) then "Infinity"
      else
        switch float2string r
        case r & (_ ++ ['.']) then snoc r '0'
        case r then r
        end
  else "NaN"

let seqToJson = lam seq : [String]. strJoin "" ["[", strJoin "," seq ,"]"]
let floatSeqToJson = lam seq : [FloatM]. seqToJson (map floatToJson seq)
let floatSeqToJson2 = lam seq : [[FloatM]]. seqToJson (map floatSeqToJson seq)
let floatSeqToJson3 = lam seq : [[[FloatM]]]. seqToJson (map floatSeqToJson2 seq)
let floatSeqToJson4 = lam seq : [[[[FloatM]]]]. seqToJson (map floatSeqToJson3 seq)
let jsonField = lam t : (String, String). strJoin "" ["\"", t.0, "\":", t.1]

let jsonObject = lam content : [(String, String)].
  strJoin "" ["{", strJoin "," (map jsonField content), "}"]

mexpr

-- Dummy infer to prevent wrapping the whole program in an infer
let m = lam t : (). () in
let d = infer (Importance { particles = 1 }) m in
()
