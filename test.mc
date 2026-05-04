-- -*- compile-command: "cppl --dppl-typecheck test.mc"; -*-

mexpr

let m = lam t : (). () in
infer (Importance { particles = 1 }) m;

0
