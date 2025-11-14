/-

      Type check core DPPL terms. The type-system is based on the simply typed
      lambda calculus and therefore more restrictive than the MExpr type-system
      which includes type inference. In this type system, float types have
      additional annotations related to smoothness. A term that type-checks with
      this type checker should type-check in MExpr (after dropping annotations
      on float types).

-/

include "bool.mc"
include "tuple.mc"
include "result.mc"

include "./dist.mc"
include "./coreppl.mc"

-- ┌───────────────────────────────┐
-- │ Effect and Coeffect Modifiers │
-- └───────────────────────────────┘

-- Effects are either deterministic (D) or random (R).
type DTCEffect
con ModD : () -> DTCEffect
con ModR : () -> DTCEffect

let dtcEffectToString : DTCEffect -> String = lam e.
  switch e
  case ModD _ then "ModD"
  case ModR _ then "ModR"
  end

-- Less than or equal over effects (e ≤ e), where D < R.
let dtcLeqe : DTCEffect -> DTCEffect -> Bool
  = lam a. lam b.
    switch (a, b)
    case (_, ModR _) then true
    case (ModR _, _) then false
    case (ModD _, _) then true
    case (_, ModD _) then false
    end

utest dtcLeqe (ModD ()) (ModD ()) with true
utest dtcLeqe (ModD ()) (ModR ()) with true
utest dtcLeqe (ModR ()) (ModD ()) with false
utest dtcLeqe (ModR ()) (ModR ()) with true

-- The greatest lower bound of two effects.
let dtcGlbe : DTCEffect -> DTCEffect -> DTCEffect
  = lam a. lam b.
    switch (a, b)
    case (ModD _, _) then a
    case (_ , ModD _) then b
    case _ then a
    end

utest dtcGlbe (ModD ()) (ModD ()) with ModD ()
utest dtcGlbe (ModD ()) (ModR ()) with ModD ()
utest dtcGlbe (ModR ()) (ModD ()) with ModD ()
utest dtcGlbe (ModR ()) (ModR ()) with ModR ()

-- The least upper bound of two effects.
let dtcLube : DTCEffect -> DTCEffect -> DTCEffect
  = lam a. lam b.
    switch (a, b)
    case (ModR _, _) then a
    case (_ , ModR _) then b
    case _ then a
    end

utest dtcLube (ModD ()) (ModD ()) with ModD ()
utest dtcLube (ModD ()) (ModR ()) with ModR ()
utest dtcLube (ModR ()) (ModD ()) with ModR ()
utest dtcLube (ModR ()) (ModR ()) with ModR ()

-- Multiplication over effects (e ⋅ e).
let dtcMule : DTCEffect -> DTCEffect -> DTCEffect
  = dtcLube

utest dtcMule (ModD ()) (ModD ()) with (ModD ())
utest dtcMule (ModD ()) (ModR ()) with (ModR ())
utest dtcMule (ModR ()) (ModD ()) with (ModR ())
utest dtcMule (ModR ()) (ModR ()) with (ModR ())

-- Equality over effects (e = e).
let dtcEqe : DTCEffect -> DTCEffect -> Bool
  = lam a. lam b.
    switch (a, b)
    case (ModD _, ModD _) | (ModR _, ModR _) then true
    case _ then false
    end

utest dtcEqe (ModD ()) (ModD ()) with true
utest dtcEqe (ModD ()) (ModR ()) with false
utest dtcEqe (ModR ()) (ModD ()) with false
utest dtcEqe (ModR ()) (ModR ()) with true

-- Coeffects are either analytic (A), piecewise analytic under analytic
-- partitioning (P), continuous (C), P and C (PC), or measurable (M).
type DTCCoeffect
con ModA  : () -> DTCCoeffect
con ModPC : () -> DTCCoeffect
con ModP  : () -> DTCCoeffect
con ModC  : () -> DTCCoeffect
con ModM  : () -> DTCCoeffect

let dtcCoeffectToString : DTCCoeffect -> String = lam c.
  switch c
  case ModA _  then "ModA"
  case ModPC _ then "ModPC"
  case ModP _  then "ModP"
  case ModC _  then "ModC"
  case ModM _  then "ModM"
  end

let _dtcCoeffectToInt : DTCCoeffect -> Int = lam c.
  switch c
  case ModM  _          then 0
  case ModC  _ | ModP _ then 1   -- NOTE(oerikss, 2025-10-13): We cannot order C and P.
  case ModPC _          then 2
  case ModA  _          then 3
  end

-- Less than or equal over coeffects (c ≤ c), where M < P < A and M < C < A.
let dtcLeqc : DTCCoeffect -> DTCCoeffect -> Bool
  = lam a. lam b.
    match (a, b) with (ModC _, ModP _) | (ModP _, ModC _) then false
    else leqi (_dtcCoeffectToInt a) (_dtcCoeffectToInt b)

utest dtcLeqc (ModA ()) (ModA ())   with true
utest dtcLeqc (ModA ()) (ModPC ())  with false
utest dtcLeqc (ModA ()) (ModP ())   with false
utest dtcLeqc (ModA ()) (ModC ())   with false
utest dtcLeqc (ModA ()) (ModM ())   with false

utest dtcLeqc (ModPC ()) (ModA ())  with true
utest dtcLeqc (ModPC ()) (ModPC ()) with true
utest dtcLeqc (ModPC ()) (ModP ())  with false
utest dtcLeqc (ModPC ()) (ModC ())  with false
utest dtcLeqc (ModPC ()) (ModM ())  with false

utest dtcLeqc (ModP ()) (ModA ())   with true
utest dtcLeqc (ModP ()) (ModPC ())  with true
utest dtcLeqc (ModP ()) (ModP ())   with true
utest dtcLeqc (ModP ()) (ModC ())   with false
utest dtcLeqc (ModP ()) (ModM ())   with false

utest dtcLeqc (ModC ()) (ModA ())   with true
utest dtcLeqc (ModC ()) (ModPC ())  with true
utest dtcLeqc (ModC ()) (ModP ())   with false
utest dtcLeqc (ModC ()) (ModC ())   with true
utest dtcLeqc (ModC ()) (ModM ())   with false

utest dtcLeqc (ModM ()) (ModA ())   with true
utest dtcLeqc (ModM ()) (ModPC ())  with true
utest dtcLeqc (ModM ()) (ModP ())   with true
utest dtcLeqc (ModM ()) (ModC ())   with true
utest dtcLeqc (ModM ()) (ModM ())   with true

-- Equality over coeffects (c = c).
let dtcEqc : DTCCoeffect -> DTCCoeffect -> Bool
  = lam a. lam b.
    switch (a, b)
    case (ModM _, ModM _)
       | (ModC _, ModC _)
       | (ModP _, ModP _)
       | (ModPC _, ModPC _)
       | (ModA _, ModA _) then true
    case _ then false
    end

utest dtcEqc (ModA ()) (ModA ())   with true
utest dtcEqc (ModA ()) (ModPC ())  with false
utest dtcEqc (ModA ()) (ModP ())   with false
utest dtcEqc (ModA ()) (ModC ())   with false
utest dtcEqc (ModA ()) (ModM ())   with false

utest dtcEqc (ModPC ()) (ModA ())  with false
utest dtcEqc (ModPC ()) (ModPC ()) with true
utest dtcEqc (ModPC ()) (ModP ())  with false
utest dtcEqc (ModPC ()) (ModC ())  with false
utest dtcEqc (ModPC ()) (ModM ())  with false

utest dtcEqc (ModP ()) (ModA ())   with false
utest dtcEqc (ModP ()) (ModPC ())  with false
utest dtcEqc (ModP ()) (ModP ())   with true
utest dtcEqc (ModP ()) (ModC ())   with false
utest dtcEqc (ModP ()) (ModM ())   with false

utest dtcEqc (ModC ()) (ModA ())   with false
utest dtcEqc (ModC ()) (ModPC ())  with false
utest dtcEqc (ModC ()) (ModP ())   with false
utest dtcEqc (ModC ()) (ModC ())   with true
utest dtcEqc (ModC ()) (ModM ())   with false

utest dtcEqc (ModM ()) (ModA ())   with false
utest dtcEqc (ModM ()) (ModPC ())  with false
utest dtcEqc (ModM ()) (ModP ())   with false
utest dtcEqc (ModM ()) (ModC ())   with false
utest dtcEqc (ModM ()) (ModM ())   with true

-- Greates lower bound of two coeffects.
let dtcGlbc : DTCCoeffect -> DTCCoeffect -> DTCCoeffect
  = lam a. lam b.
    switch (a, b)
    case (ModM _, _) | (_, ModM _) then ModM ()
    case (ModC _, ModP _) | (ModP _, ModC _) then ModM ()
    case (ModC _, _) | (_, ModC _) then ModC ()
    case (ModP _, _) | (_, ModP _) then ModP ()
    case (ModPC _, _) | (_, ModPC _) then ModPC ()
    case (ModA _, ModA _) | (ModA _, ModA _) then ModA ()
    end

utest dtcGlbc (ModA ()) (ModA ())   with (ModA ())
utest dtcGlbc (ModA ()) (ModPC ())  with (ModPC ())
utest dtcGlbc (ModA ()) (ModP ())   with (ModP ())
utest dtcGlbc (ModA ()) (ModC ())   with (ModC ())
utest dtcGlbc (ModA ()) (ModM ())   with (ModM ())

utest dtcGlbc (ModPC ()) (ModA ())  with (ModPC ())
utest dtcGlbc (ModPC ()) (ModPC ()) with (ModPC ())
utest dtcGlbc (ModPC ()) (ModP ())  with (ModP ())
utest dtcGlbc (ModPC ()) (ModC ())  with (ModC ())
utest dtcGlbc (ModPC ()) (ModM ())  with (ModM ())

utest dtcGlbc (ModP ()) (ModA ())   with (ModP ())
utest dtcGlbc (ModP ()) (ModPC ())  with (ModP ())
utest dtcGlbc (ModP ()) (ModP ())   with (ModP ())
utest dtcGlbc (ModP ()) (ModC ())   with (ModM ())
utest dtcGlbc (ModP ()) (ModM ())   with (ModM ())

utest dtcGlbc (ModC ()) (ModA ())   with (ModC ())
utest dtcGlbc (ModC ()) (ModPC ())  with (ModC ())
utest dtcGlbc (ModC ()) (ModP ())   with (ModM ())
utest dtcGlbc (ModC ()) (ModC ())   with (ModC ())
utest dtcGlbc (ModC ()) (ModM ())   with (ModM ())

utest dtcGlbc (ModM ()) (ModA ())   with (ModM ())
utest dtcGlbc (ModM ()) (ModPC ())  with (ModM ())
utest dtcGlbc (ModM ()) (ModP ())   with (ModM ())
utest dtcGlbc (ModM ()) (ModC ())   with (ModM ())
utest dtcGlbc (ModM ()) (ModM ())   with (ModM ())

-- Least upper bound of two coeffects.
let dtcLubc : DTCCoeffect -> DTCCoeffect -> DTCCoeffect
  = lam a. lam b.
    switch (a, b)
    case (ModA _, _) | (_, ModA _) then ModA ()
    case (ModPC _, _) | (_, ModPC _) then ModPC ()
    case (ModP _, ModC _) | (ModC _, ModP _) then ModPC ()
    case (ModP _, _) | (_, ModP _) then ModP ()
    case (ModC _, _) | (_, ModC _) then ModC ()
    case (ModM _, ModM _) | (ModM _, ModM _) then ModM ()
    end

utest dtcLubc (ModA ()) (ModA ())   with (ModA ())
utest dtcLubc (ModA ()) (ModPC ())  with (ModA ())
utest dtcLubc (ModA ()) (ModP ())   with (ModA ())
utest dtcLubc (ModA ()) (ModC ())   with (ModA ())
utest dtcLubc (ModA ()) (ModM ())   with (ModA ())

utest dtcLubc (ModPC ()) (ModA ())  with (ModA ())
utest dtcLubc (ModPC ()) (ModPC ()) with (ModPC ())
utest dtcLubc (ModPC ()) (ModP ())  with (ModPC ())
utest dtcLubc (ModPC ()) (ModC ())  with (ModPC ())
utest dtcLubc (ModPC ()) (ModM ())  with (ModPC ())

utest dtcLubc (ModP ()) (ModA ())   with (ModA ())
utest dtcLubc (ModP ()) (ModPC ())  with (ModPC ())
utest dtcLubc (ModP ()) (ModP ())   with (ModP ())
utest dtcLubc (ModP ()) (ModC ())   with (ModPC ())
utest dtcLubc (ModP ()) (ModM ())   with (ModP ())

utest dtcLubc (ModC ()) (ModA ())   with (ModA ())
utest dtcLubc (ModC ()) (ModPC ())  with (ModPC ())
utest dtcLubc (ModC ()) (ModP ())   with (ModPC ())
utest dtcLubc (ModC ()) (ModC ())   with (ModC ())
utest dtcLubc (ModC ()) (ModM ())   with (ModC ())

utest dtcLubc (ModM ()) (ModA ())   with (ModA ())
utest dtcLubc (ModM ()) (ModPC ())  with (ModPC ())
utest dtcLubc (ModM ()) (ModP ())   with (ModP ())
utest dtcLubc (ModM ()) (ModC ())   with (ModC ())
utest dtcLubc (ModM ()) (ModM ())   with (ModM ())

-- Multiplication over coeffects (c ⋅ c).
let dtcMulc : DTCCoeffect -> DTCCoeffect -> DTCCoeffect = dtcGlbc

-- ┌───────────────┐
-- │ Annotated AST │
-- └───────────────┘

lang DTCAstBase = Ast + Eq
  -- NOTE(oerikss, 2024-10-07): The semantic functions in this fragment assumes
  -- that types and terms have been symbolized. I.e., it relies on unique
  -- identifiers in types and terms.

  -- `dtcLeqc` overloaded to types (c ≤ T).
  sem leqcType : DTCCoeffect -> Type -> Bool
  sem leqcType c =| ty -> true

  -- `dtcLeqc` overloaded to types (T ≤ c).
  sem leqTypec : Type -> DTCCoeffect -> Bool
  sem leqTypec ty =| c -> leqTypecH (ty, c)

  sem leqTypecH : (Type, DTCCoeffect) -> Bool
  sem leqTypecH =| (ty, c) -> true

  -- `dtcEqc` overloaded to types (types that do not represent vectors are
  -- assumed to have `M` modifiers).
  sem eqcType : DTCCoeffect -> Type -> Bool
  sem eqcType c =| ty -> dtcEqc c (ModM ())

  -- "Scalar multiplication" of coeffects over types (c ⋅ T).
  sem mulcType : DTCCoeffect -> Type -> Type
  sem mulcType c =| ty -> ty

  -- Least upper bound coeffect modifier of type (types that do not represent
  -- vectors are assumed to have `M` modifiers).
  sem lubcType : Type -> DTCCoeffect
  sem lubcType =| _ -> ModM ()

  -- Greatest lower bound coeffect modifier of type (types that do not represent
  -- vectors are assumed to have `A` modifiers).
  sem glbcType : Type -> DTCCoeffect
  sem glbcType =| _ -> ModA ()

  -- Drops decorations from types
  sem eraseDecorationsType : Type -> Type
  sem eraseDecorationsType =| ty -> smap_Type_Type eraseDecorationsType ty

  -- Drops decorations from terms
  sem eraseDecorations : Expr -> Expr
  sem eraseDecorations =| tm ->
    smap_Expr_Expr eraseDecorations (smap_Expr_Type eraseDecorationsType tm)

  -- Subtyping and type promotion
  -- NOTE(oerikss, 2024-10-04): The defualt case only compares contructors of
  -- the types. The extension of `DTCAstBase` are reponsible to handle all
  -- cases where `subtype` needs to be applied recursively.

  -- `subtype (lhs, rhs)` is true if `lhs` is a subtype of `rhs`
  sem subtype : (Type, Type) -> Bool
  sem subtype =| (lhs, rhs) -> eqi (constructorTag lhs) (constructorTag rhs)

  -- `joinType (lhs, rhs)` returns the join of `lhs` and `rhs` if there is such
  -- as concrete type. Otherwise it returns `None ()` which can be considered
  -- the top type.
  sem joinType : (Type, Type) -> Option Type
  sem joinType =| (lhs, rhs) ->
    if eqi (constructorTag lhs) (constructorTag rhs) then Some lhs else None ()

  -- `meetType (lhs, rhs)` returns the meet of `lhs` and `rhs` if there is such
  -- as concrete type. Otherwise it returns `None ()` which can be considered
  -- the bottom type.
  sem meetType : (Type, Type) -> Option Type
  sem meetType =| (lhs, rhs) ->
    if eqi (constructorTag lhs) (constructorTag rhs) then Some lhs else None ()

  -- Converts between MExpr types and DDPL types. In particular it replaces
  -- MExpr float and arrow types to the corresponding DPPL types.
  sem fromMExprTy : Type -> Type
  sem fromMExprTy =| ty -> smap_Type_Type fromMExprTy ty

  -- Sets the coeffects modifier on a type.
  sem setC : DTCCoeffect -> Type -> Type
  sem setC c =| ty -> smap_Type_Type (setC c) ty

  -- Is this typem forst order. Defaults to true so higher order types should
  -- extend this.
  sem isFirstOrder : Type -> Bool
  sem isFirstOrder =| ty ->
    sfold_Type_Type (lam acc. lam ty. and acc (isFirstOrder ty)) true ty
end

lang DTCBottomTypeAst = DTCAstBase + UnknownTypeAst + PrettyPrint
  syn Type =| TyBot {info : Info}

  -- Setters/Getters
  sem tyWithInfo info =| TyBot r -> TyBot { r with info = info }
  sem infoTy =| TyBot r -> r.info

  -- Eq
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyBot r ->
    match unwrapType lhs with TyBot l then Some free
    else None ()

  -- Pprint
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyBot r -> (env, "Bot")

  -- Conversions
  sem eraseDecorationsType =
  | TyBot r -> TyUnknown { info = r.info }

  -- Coeffect/Type operations
  sem subtype =
  | (TyBot _, _) -> true
  | (! TyBot _, TyBot _) -> false

  sem joinType =
  | (TyBot _, ty) | (ty, TyBot _) -> Some ty
end

let tybot_ = use DTCBottomTypeAst in TyBot { info = NoInfo () }

lang DTCFloatTypeAst = DTCAstBase + FloatTypeAst + PrettyPrint
  -- Float types are annotated with coffects
  syn Type =| TyFloatC {info : Info, c : DTCCoeffect}

  -- Setters/Getters
  sem tyWithInfo info =| TyFloatC r -> TyFloatC { r with info = info }
  sem infoTy =| TyFloatC r -> r.info

  -- Eq
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyFloatC r ->
    match unwrapType lhs with TyFloatC l then
      if dtcEqc l.c r.c then Some free else None ()
    else None ()

  -- PPrint
  sem typePrecedence = | TyFloatC _ -> 1
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyFloatC (r & {c = ModA _}) -> (env, "FloatA")
  | TyFloatC (r & {c = ModPC _}) -> (env, "FloatPC")
  | TyFloatC (r & {c = ModP _}) -> (env, "FloatP")
  | TyFloatC (r & {c = ModC _}) -> (env, "FloatC")
  | TyFloatC (r & {c = ModM _}) -> (env, "FloatM")

  -- Builder
  sem tyfloatc_ : DTCCoeffect -> Type
  sem tyfloatc_ =| c -> TyFloatC { info = NoInfo (), c = c }

  sem ityfloatc_ : Info -> DTCCoeffect -> Type
  sem ityfloatc_ info =| c -> TyFloatC { info = info, c = c }

  -- Conversions
  sem eraseDecorationsType =
  | TyFloatC r -> TyFloat { info = r.info }

  sem fromMExprTy =
  | TyFloat r -> ityfloatc_ r.info (ModM ())

  -- Coeffect/Type operations
  sem leqcType c =
  | TyFloatC r -> dtcLeqc c r.c

  sem leqTypecH =
  | (TyFloatC r, c) -> dtcLeqc r.c c

  sem eqcType c =
  | TyFloatC r -> dtcEqc c r.c

  sem mulcType c =
  | TyFloatC r -> TyFloatC { r with c = dtcMulc c r.c }

  sem lubcType =
  | TyFloatC r -> r.c

  sem glbcType =
  | TyFloatC r -> r.c

  sem subtype =
  | (TyFloatC l, TyFloatC r) -> dtcLeqc l.c r.c

  sem joinType =
  | (TyFloatC l, TyFloatC r) ->
    Some (TyFloatC { l with c = dtcLubc l.c r.c })

  sem meetType =
  | (TyFloatC l, TyFloatC r) ->
    Some (TyFloatC { l with c = dtcGlbc l.c r.c })

  sem setC c =
  | TyFloatC r -> TyFloatC { r with c = c }
end

lang DTCFunTypeAst = DTCAstBase + FunTypeAst + PrettyPrint
  -- Arrow types are annotated with effects
  syn Type =| TyArrowCE {
    info : Info, from : Type, to : Type, c: DTCCoeffect, e : DTCEffect }

  -- Setters/Getters
  sem tyWithInfo info =| TyArrowCE r -> TyArrowCE {r with info = info}
  sem infoTy =| TyArrowCE r -> r.info

  -- Shallow map/fold
  sem smapAccumL_Type_Type f acc =
  | TyArrowCE r ->
    match f acc r.from with (acc, from) in
    match f acc r.to with (acc, to) in
    (acc, TyArrowCE {r with from = from, to = to})

  -- Eq
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyArrowCE r ->
    match unwrapType lhs with TyArrowCE l then
      match eqTypeH typeEnv free l.from r.from with Some free then
        if dtcEqc l.c r.c then
          if dtcEqe l.e r.e then eqTypeH typeEnv free l.to r.to
          else None ()
        else None ()
      else None ()
    else None ()

  -- Pprint
  sem typePrecedence =
  | TyArrowCE _ -> 0

  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyArrowCE r ->
    switch (r.c, r.e)
    case (ModA _, ModD _) then
      getTypeStringCode indent env (tyarrow_ r.from r.to)
    case (ModA _, e) then
      match printTypeParen indent 1 env r.from with (env, from) in
      match printTypeParen indent 2 env r.to with (env, to) in
      (env, join [from, " ->", dtcEffectToString e, " ", to])
    case (c, ModD _) then
      match printTypeParen indent 1 env r.from with (env, from) in
      match printTypeParen indent 2 env r.to with (env, to) in
      (env, join [from, " ->", dtcCoeffectToString c, " ", to])
    case (c, e) then
      match printTypeParen indent 1 env r.from with (env, from) in
      match printTypeParen indent 2 env r.to with (env, to) in
      (env, join [
        from, " ->",
        dtcCoeffectToString c,
        "(", dtcEffectToString e, " ",
        to, ")" ])
    end

  -- Builder
  sem tyarrowce_ : Type -> Type -> DTCCoeffect -> DTCEffect -> Type
  sem tyarrowce_ from to c =| e ->
    TyArrowCE { info = NoInfo (), from = from, to = to, c = c, e = e }

  sem ityarrowe_ : Info -> Type -> Type -> DTCCoeffect -> DTCEffect -> Type
  sem ityarrowe_ info from to c =| e ->
    TyArrowCE { info = info, from = from, to = to, c = c, e = e }

  -- Conversions
  sem eraseDecorationsType =
  | TyArrowCE r ->
    smap_Type_Type eraseDecorationsType
      (TyArrow { info = r.info, from = r.from, to = r.to })

  sem fromMExprTy =
  | TyArrow r ->
    smap_Type_Type fromMExprTy (ityarrowe_ r.info r.from r.to (ModA ()) (ModD ()))

  -- Coeffect/Type operations
  sem leqcType c =
  | TyArrowCE r -> dtcLeqc c r.c

  sem leqTypecH =
  | (TyArrowCE r, c) -> dtcLeqc r.c c

  sem eqcType c =
  | TyArrowCE r -> dtcEqc c r.c

  sem mulcType c =
  | TyArrowCE r -> TyArrowCE { r with c = dtcMulc c r.c }

  sem lubcType =
  | TyArrowCE r -> r.c

  sem glbcType =
  | TyArrowCE r -> r.c

  sem subtype c =
  | (TyArrowCE l, TyArrowCE r) ->
    allb [
      subtype (r.from, l.from),
      subtype (l.to, r.to),
      dtcLeqc l.c r.c,
      dtcLeqe l.e r.e
    ]

  sem joinType =
  | (TyArrowCE l, TyArrowCE r) ->
    optionBind (meetType (l.from, r.from)) (lam from.
      optionBind (joinType (l.to, r.to)) (lam to.
        Some
          (TyArrowCE { l with from = from, to = to,
                       c = dtcLubc l.c r.c, e = dtcLube l.e r.e })))


  sem meetType =
  | (TyArrowCE l, TyArrowCE r) ->
    optionBind (joinType (l.from, r.from)) (lam from.
      optionBind (meetType (l.to, r.to)) (lam to.
        Some
          (TyArrowCE { l with from = from, to = to,
                       c = dtcGlbc l.c r.c, e = dtcGlbe l.e r.e })))

  sem setC c =
  | TyArrowCE r -> TyArrowCE { r with c = c }

  sem isFirstOrder =
  | TyArrowCE r -> false

  -- This function uncurries a term by multiplying the coeffects on the arrow
  -- types. This is helpful when typechecking higher-order terms and intrinsics.
  sem uncurryExpr : Expr -> Expr
  sem uncurryExpr =| tm ->
    recursive let recur = lam tys. lam ty.
      match ty with TyArrowCE r then recur (snoc tys r.from) r.to
      else tys
    in
    let tys = recur [] in
    if null tys then tm
    else
      let info = infoTm tm in
      let wi = withInfo info in
      let id = nameSym "x" in
      let var = wi (nvar_ id) in
      tmLam info tyunknown_ id (itytuple_ info tys)
        (foldl (lam tm. lam i. wi (app_ tm (wi (tupleproj_ i var))))
           tm (create (length tys) (lam i. i)))
end

lang DTCSeqTypeAst = DTCAstBase + SeqTypeAst
  sem leqcType c =
  | ty & TySeq _ ->
    sfold_Type_Type (lam b. lam ty. and b (leqcType c ty)) true ty

  sem leqTypecH =
  | (ty & TySeq _, c) ->
    sfold_Type_Type (lam b. lam ty. and b (leqTypec ty c)) true ty

  sem eqcType c =
  | ty & TySeq _ ->
    sfold_Type_Type (lam b. lam ty. and b (eqcType c ty)) true ty

  sem mulcType c =
  | ty & TySeq _ -> smap_Type_Type (mulcType c) ty

  sem lubcType =
  | TySeq r -> lubcType r.ty

  sem glbcType =
  | TySeq r -> glbcType r.ty

  sem subtype =
  | (TySeq l, TySeq r) -> subtype (l.ty, r.ty)

  sem _dtcSeqJoinMeet f l =| r ->
    optionMap (lam ty. TySeq { l with ty = ty }) (f (l.ty, r.ty))

  sem joinType =
  | (TySeq l, TySeq r) -> _dtcSeqJoinMeet joinType l r

  sem meetType =
  | (TySeq l, TySeq r) -> _dtcSeqJoinMeet meetType l r
end

lang DTCRecordTypeAst = DTCAstBase + RecordTypeAst
  sem leqcType c =
  | ty & TyRecord _ ->
    sfold_Type_Type (lam b. lam ty. and b (leqcType c ty)) true ty

  sem leqTypecH =
  | (ty & TyRecord _, c) ->
    sfold_Type_Type (lam b. lam ty. and b (leqTypec ty c)) true ty

  sem eqcType c =
  | ty & TyRecord _ ->
    sfold_Type_Type (lam b. lam ty. and b (eqcType c ty)) true ty

  sem mulcType c =
  | ty & TyRecord _ -> smap_Type_Type (mulcType c) ty

  sem lubcType =
  | ty & TyRecord _ ->
    sfold_Type_Type (lam c. lam ty. dtcLubc c (lubcType ty)) (ModM ()) ty

  sem glbcType =
  | ty & (TyRecord _) ->
    sfold_Type_Type (lam c. lam ty. dtcGlbc c (glbcType ty)) (ModA ()) ty

  sem subtype =
  | (TyRecord l, TyRecord r) ->
    let m = mapMerge
              (lam l. lam r.
                switch (l, r)
                case (None _, _) | (_, None _) then Some false
                case (Some l, Some r) then Some (subtype (l, r))
                end)
              l.fields r.fields
    in
    mapAll (lam x. x) m

  sem _dtcRecordJoinMeet f l =| r ->
    let nl = mapSize l.fields in
    if eqi nl (mapSize r.fields) then
      let fields =
        mapMerge
          (lam l. lam r.
            switch (l, r)
            case (None _, _) | (_, None _) then None ()
            case (Some l, Some r) then f (l, r)
            end)
          l.fields r.fields
      in
      if eqi nl (mapSize fields) then
        Some (TyRecord { l with fields = fields })
      else None ()
    else None ()

  sem joinType =
  | (TyRecord l, TyRecord r) -> _dtcRecordJoinMeet joinType l r

  sem meetType =
  | (TyRecord l, TyRecord r) -> _dtcRecordJoinMeet meetType l r
end

lang DTCVarTypeAst = DTCAstBase + VarTypeAst
  sem subtype =
  | (TyVar l, TyVar r) -> nameEq l.ident r.ident

  sem joinType =
  | (TyVar l, TyVar r) ->
    if nameEq l.ident r.ident then Some (TyVar l)
    else None ()

  sem meetType =
  | arg & (TyVar _, TyVar _) -> joinType arg
end

lang DTCDistTypeAst =  DTCAstBase + Dist
  sem subtype =
  | (TyDist l, TyDist r) -> subtype (l.ty, r.ty)

  sem _dtcDistJoinMeet f l =| r ->
    optionBind (f (l.ty, r.ty)) (lam ty. Some (TyDist { l with ty = ty }))

  sem joinType =
  | (TyDist l, TyDist r) -> _dtcDistJoinMeet joinType l r

  sem meetType =
  | (TyDist l, TyDist r) -> _dtcDistJoinMeet meetType l r

  sem mulcType c =
  | TyDist r -> TyDist r
end

lang DTCAst = DTCAstBase +
  DTCBottomTypeAst +
  DTCFloatTypeAst +
  DTCFunTypeAst +
  DTCSeqTypeAst +
  DTCRecordTypeAst +
  DTCVarTypeAst +
  DTCDistTypeAst
end


-- ┌──────────────────┐
-- │ Type Environment │
-- └──────────────────┘

lang DTCEnv = DTCAst + PrettyPrint
  -- Fragment defining and implementing DPPL type environment

  type DTCEnv = Map Name Type

  -- Basic creation/accessing/manipulation/conversion.
  sem dtcEnvOfSeq : [(Name, Type)] -> DTCEnv
  sem dtcEnvOfSeq =| seq -> mapFromSeq nameCmp seq

  sem dtcEnvToSeq : DTCEnv -> [(Name, Type)]
  sem dtcEnvToSeq =| env -> mapToSeq env

  -- `dtcLeqc` overloaded to type environments (c ≤ Γ).
  sem dtcLeqcEnv : DTCCoeffect -> DTCEnv -> Bool
  sem dtcLeqcEnv c =| env -> mapAll (leqcType c) env

  -- `dtcLeqc` overloaded to type environments (Γ ≤ c).
  sem dtcLeqEnvc : DTCEnv -> DTCCoeffect -> Bool
  sem dtcLeqEnvc env =| c -> mapAll (lam ty. leqTypec ty c) env

  -- The domain of the type environment.
  sem dtcEnvDomain : DTCCoeffect -> Set Name
  sem dtcEnvDomain =| env -> setOfKeys env

  -- Looks up the type associated with an identifier in the type environment if
  -- there is a binding for the particular identifier. Otherwise this function
  -- return `None ()`.
  sem dtcEnvLookup : Name -> DTCEnv -> Option Type
  sem dtcEnvLookup ident =| env ->
    -- NOTE(oerikss, 2024-10-07): A difference here from the formalization is
    -- that we do not require `env` to be a singleton. If it is not, we can
    -- always implicitly apply the rule T-Weaken until it is a singleton.
    mapLookup ident env

  -- Inserts a binding in the type environment.
  sem dtcEnvInsert : Name -> Type -> DTCEnv -> DTCEnv
  sem dtcEnvInsert ident ty =| env -> mapInsert ident ty env

  -- Inserts a bindings in the type environment.
  sem dtcEnvBatchInsert : Map Name Type -> DTCEnv -> DTCEnv
  sem dtcEnvBatchInsert batch =| env ->
    mapMerge
      (lam a. lam b.
      switch (a, b)
      case (None _, ty) | (ty, None _) then ty
      case (Some _, Some _) then error (strJoin " " [
        "Found overlapping identifiers in dtcEnvBatchInsert",
        "which should not be possible in a symbolized program"])
      end)
      batch env

  -- Weaken the type environment by removing a set of identifiers from its
  -- domain.
  sem dtcEnvWeaken : Set Name -> DTCEnv -> DTCEnv
  sem dtcEnvWeaken idents =| env ->
    mapFilterWithKey (lam ident. lam. setMem ident idents) env

  -- Returns the greatest lower bound of coeffect modifiers in the environment.
  sem dtcEnvGlbc : DTCEnv -> DTCCoeffect
  sem dtcEnvGlbc =| env ->
    mapFoldWithKey (lam c. lam. lam ty. dtcGlbc c (glbcType ty)) (ModA ()) env

  -- Returns the least upper bound of coeffect modifiers in the environment.
  sem dtcEnvLubc : DTCEnv -> DTCCoeffect
  sem dtcEnvLubc =| env ->
    mapFoldWithKey (lam c. lam. lam ty. dtcLubc c (lubcType ty)) (ModM ()) env

  -- String representation of the typing environment
  sem dtcEnvToString : DTCEnv -> String
  sem dtcEnvToString =| env ->
    strJoin ", "
      (map (lam t. join [nameGetStr t.0, ":", type2str t.1]) (dtcEnvToSeq env))
end


-- ┌──────────────┐
-- │ Type Checker │
-- └──────────────┘

lang DTCTypeError = Ast + DTCEnv + DTCFloatTypeAst + PrettyPrint
  syn DTCTypeError =
  -- NOTE(oerikss, 2024-10-08): The error parameters are optional to make
  -- testing errors easier.
  | DTCArrowError (Info, Option Type)
  | DTCArgError (Info, Option (Type, Type))
  | DTCJoinError (Info, Option (Type, Type))
  | DTCPatError (Info, Option Type)
  | DTCAnotError Info
  | DTCSolveODEModelError (Info, Option Type)
  | DTCDiffFnError (Info, Option (DTCCoeffect, Type))
  | DTCPolyDistError Info
  | DTCPolyConstError Info
  | DTCUnuspportedTermError (Info, Option Expr)
  | DTCInvalidContextError (Info, Option (Name))
  | DTCContextConstraintError (Info, Option (DTCCoeffect,  DTCEnv))
  | DTCHigherOrderTypeError (Info, Option Type)
  | DTCTypeConstraintErrorR (Info, Option (DTCCoeffect, Type))

  sem typeErrorInfo : DTCTypeError -> Info
  sem typeErrorInfo =
  | DTCArrowError (i, _)
  | DTCArgError (i, _)
  | DTCJoinError (i, _)
  | DTCPatError (i, _)
  | DTCAnotError i
  | DTCSolveODEModelError (i, _)
  | DTCDiffFnError (i, _)
  | DTCPolyDistError i
  | DTCPolyConstError i
  | DTCUnuspportedTermError (i, _) -> i
  | DTCInvalidContextError (i, _)
  | DTCContextConstraintError (i, _) -> i
  | DTCHigherOrderTypeError (i, _) -> i
  | DTCTypeConstraintErrorR (i, _) -> i

  sem typeErrorToString : DTCTypeError -> String
  sem typeErrorToString =
  | DTCArrowError _ -> "ArrowError"
  | DTCArgError _ -> "ArgError"
  | DTCJoinError _ -> "JoinError"
  | DTCPatError _ -> "PatError"
  | DTCAnotError _ -> "AnotError"
  | DTCSolveODEModelError _ -> "SolveODEModelError"
  | DTCDiffFnError _ -> "DiffFnError"
  | DTCPolyDistError _ -> "PolyDistError"
  | DTCPolyConstError _ -> "PolyConstError"
  | DTCUnuspportedTermError _ -> "UnuspportedTermError"
  | DTCInvalidContextError _ -> "InvalidContextError"
  | DTCContextConstraintError _ -> "ContextConstraintError"
  | DTCHigherOrderTypeError _ -> "HigherOrderTypeError"
  | DTCTypeConstraintErrorR _ -> "TypeConstraintErrorR"

  sem typeErrorToMsg : DTCTypeError -> (Info, String)
  sem typeErrorToMsg =| err ->
    match typeErrorToMsgH err with (info, msg) in
    (info, join ["* ", typeErrorToString err, ":\n", msg])

  sem typeErrorToMsgH : DTCTypeError -> (Info, String)
  sem typeErrorToMsgH =
  | DTCArrowError (info, Some ty) ->
    (info, _typeErrorToMsg2 ["Function type"] [type2str ty])
  | DTCArgError (info, Some (expected, found)) ->
    (info, _typeErrorToMsg2 [type2str expected] [type2str found])
  | DTCJoinError (info, Some (ty1, ty2)) ->
    (info, join [
      "* Cannot join: ", type2str ty1, "\n",
      "*       with: ", type2str ty2])
  | DTCPatError (info, Some ty) ->
    (info, join ["* Pattern does not match type: ", type2str ty])
  | DTCAnotError info ->
    (info, join ["* Missing type annotation"])
  | DTCSolveODEModelError (info, Some ty) ->
    (info,
     _typeErrorToMsg2
       ["Determinstic function type FloatX -> T[Y] -> T,",
        join [
          "where T isomorfic to a vector of floats, and X = ",
          dtcCoeffectToString (ModA ()), " or X = ",
          dtcCoeffectToString (ModC ()),
          ", and Y = ",
          dtcCoeffectToString (ModA ()),
          "." ]]
       [type2str ty])
  | DTCDiffFnError (info, Some (c, ty)) ->
    (info,
     _typeErrorToMsg2
       ["Determinstic function type T₁ -> T₂,",
        "where T₁, T₂ are isomorfic to vectors of floats",
        (join ["and where all coeffect modifiers in T₁ are ",
               dtcCoeffectToString c, "."])]
       [type2str ty])
  | DTCPolyDistError info ->
    (info, "* Polymorfic distributions are currently not supported")
  | DTCPolyConstError info ->
    (info, join [
      "* Cannot infer the type of this polymorphic intrinsic.\n",
      "* Try to apply it to one or more arguments."
    ])
  | DTCUnuspportedTermError (info, Some tm) ->
    dprint tm;
    (info, strJoin "\n" ["* This term is currently not supported:", expr2str tm])
  | DTCInvalidContextError (info, Some name) ->
    (info, join [
      "* The variable ", nameGetStr name,
      " does not appear in the typing context.\n",
      "* This should not happen in symbolized progams."
    ])
  | DTCContextConstraintError (info, Some (c, env)) ->
    (info, join [
      "* The type context ", dtcEnvToString env, "\n",
      "* is not less than or equal to ", dtcCoeffectToString c
    ])
  | DTCHigherOrderTypeError (info, Some ty) ->
    (info, join [
      "* A higher order type is not allowed here but got:\n",
      type2str ty
    ])
  | DTCTypeConstraintErrorR (info, Some (c, ty)) ->
    (info, join [
      "* Type constriant error: ",
      dtcCoeffectToString c, " ≤ ",
      type2str ty,
      " does not hold."
    ])
  | err -> (typeErrorInfo err, "* No error message")

  sem _typeErrorToMsg2 expected =| found ->
    let nli = "\n*           " in
    join [
      "* Expected: ", strJoin nli expected, "\n",
      "*    Found: ", strJoin nli found]
end

-- ┌───────────────┐
-- │ Type of Terms │
-- └───────────────┘

lang DTCTypeOfBase = DTCTypeError + DTCEnv
  type ResultOk = {e : DTCEffect, ty : Type, fv : Set Name}

  sem weakenedMaxc : DTCEnv -> Set Name -> DTCCoeffect
  sem weakenedMaxc env =| fv -> dtcEnvLubc (dtcEnvWeaken fv env)

  sem promote : DTCEnv -> Set Name -> Type -> Type
  sem promote env =| fv -> let c = weakenedMaxc env fv in mulcType c

  sem typeOfH : DTCEnv -> Expr -> Result DTCTypeError DTCTypeError ResultOk
  sem typeOfH env =| tm ->
    result.err (DTCUnuspportedTermError (infoTm tm, Some tm))

  sem typeOfHPromote
    : DTCEnv -> Expr -> Result DTCTypeError DTCTypeError ResultOk
  sem typeOfHPromote env =| tm ->
    result.bind (typeOfH env tm) (lam tm.
      result.ok { tm with ty = promote env tm.fv tm.ty })

  sem resultOK
    : [DTCEffect] -> Type -> [Set Name]
      -> Result DTCTypeError DTCTypeError ResultOk
  sem resultOK es ty =| fvs ->
    result.ok { e = foldr1 dtcMule es, ty = ty, fv = foldr1 setUnion fvs }

  sem argErr : all a. Expr -> Type -> Type -> Result DTCTypeError DTCTypeError a
  sem argErr tm ty1 =| ty2 ->
    result.err (DTCArgError (infoTm tm, Some (ty1, ty2)))

  sem typeOf :
    DTCEnv -> Expr ->
      Result DTCTypeError DTCTypeError (DTCEffect, Type)
  sem typeOf env =| tm -> result.map (lam t. (t.e, t.ty)) (typeOfH env tm)

  sem typeOfExn : Expr -> (DTCEffect, Type)
  sem typeOfExn =| tm ->
    switch result.consume (typeOf (dtcEnvOfSeq []) tm)
    case (_, Right ty) then ty
    case (_, Left errs) then
      errorMulti (map typeErrorToMsg errs) "** TYPE ERROR **"
    end

  -- Accumulates effects and free variables while type-checking and promoting
  -- types in parallel.
  sem mapAccumLTypeOfH : DTCEnv -> [Expr] ->
    Result DTCTypeError DTCTypeError ((DTCEffect, Set Name), [Type])
  sem mapAccumLTypeOfH env =| tms ->
    result.bind (result.mapM (typeOfH env) tms) (lam rs.
      result.ok
        (mapAccumL
           (lam acc. lam r.
             match acc with (e, fv) in
             ((dtcMule e r.e, setUnion fv r.fv), promote env r.fv r.ty))
           (ModD (), setEmpty nameCmp)
           rs))

  -- Accumulates effects and free variables.
  sem foldTypeOfH :
    DTCEnv ->
      Result DTCTypeError DTCTypeError {e : DTCEffect, fv : Set Name} ->
      Expr ->
        Result DTCTypeError DTCTypeError {e : DTCEffect, fv : Set Name}
  sem foldTypeOfH env acc =| tm ->
    result.map2
      (lam l. lam r. { e = dtcMule l.e r.e, fv = setUnion l.fv r.fv })
      acc (typeOfH env tm)
end

lang DTCTypeOfVar = VarAst + DTCTypeOfBase
  sem typeOfH env =
  | TmVar r ->
    optionMapOrElse
      (lam. result.err (DTCInvalidContextError (r.info, Some (r.ident))))
      (lam ty. result.ok {
        e = ModD (),
        ty = ty,
        fv = setSingleton nameCmp r.ident })
      (dtcEnvLookup r.ident env)
end

lang DTCTypeOfLam = LamAst + DTCTypeOfBase
  sem typeOfH env =
  | TmLam (r &
    {tyAnnot = TyUnknown _}) ->
    result.err (DTCAnotError r.info)
  | TmLam r ->
    let env = dtcEnvInsert r.ident r.tyAnnot env in
    result.bind (typeOfH env r.body)
      (lam body.
        let promote = promote env in
        let fv = setRemove r.ident body.fv in
        result.ok {
          e = ModD (),
          ty = promote fv
                 (ityarrowe_ r.info r.tyAnnot
                    (promote body.fv body.ty) (ModA ()) body.e),
          fv = fv })
end

lang DTCTypeOfApp = AppAst + DTCFunTypeAst + FreeVars + DTCTypeOfBase
  sem typeOfH env =
  | TmApp r ->
    result.bind (typeOfHPromote env r.lhs) (lam lhs.
      -- NOTE(oerikss, 2025-10-01): Because T1 ->c T2 <: T1 ->A T2 for all c we
      -- do not need to check the coeffect modifier of the arrow type here and
      -- we do not need to promote the LHS.
      match lhs with {ty = TyArrowCE arr} then
        result.bind (typeOfHPromote env r.rhs) (lam rhs.
          if subtype (rhs.ty, arr.from) then
            let fv = setUnion lhs.fv rhs.fv in
            resultOK [lhs.e, arr.e, rhs.e] (promote env fv arr.to) [fv]
          else argErr r.rhs arr.from rhs.ty)
      else result.err (DTCArrowError (infoTm r.lhs, Some (lhs.ty))))
end

lang DTCTypeOfLet = DTCTypeOfLam + DTCTypeOfApp + UnknownTypeAst
  sem typeOfH env =
  | TmDecl (x & {decl = DeclLet r}) ->
    let wi = withInfo r.info in
    typeOfH env (wi (app_ (wi (nlam_ r.ident r.tyAnnot x.inexpr)) r.body))
  | TmDecl (x & {decl = DeclLet (r & {tyAnnot = TyUnknown _})}) ->
    result.bind (typeOfH env r.body) (lam body.
      typeOfH env (TmDecl {x with decl = DeclLet { r with tyAnnot = body.ty }}))
end

lang DTCTyConst = TyConst + DTCTypeError + DTCTypeOfBase

  sem dtcConstType : Info -> Const -> Result DTCTypeError DTCTypeError Type
  sem dtcConstType info =
  | const ->
    -- NOTE(oerikss, 2024-10-09): By default we type constant functions as
    -- deterministic and measurable.
    let ty = fromMExprTy (tyConst const) in
    match ty with TyAll _ then result.err (DTCPolyConstError info)
    else result.ok ty
end

lang DTCTypeOfConst =
  ConstAst + DTCTyConst + CmpFloatAst + ElementaryFunctions +
  DTCFunTypeAst + DTCTypeOfBase

  sem typeOfH env =
  | TmConst r ->
    result.bind (dtcConstType r.info r.val)
      (lam ty. result.ok { e = ModD (), ty = ty, fv = setEmpty nameCmp })
end

lang DTCTypeOfSeq = SeqAst + SeqTypeAst + DTCTypeOfBase
  sem typeOfH env =
  | TmSeq (r & {tms = []}) ->
    result.ok {
      e = ModD (),
      ty = ityseq_ r.info (TyBot { info = r.info }),
      fv = setEmpty nameCmp
    }
  | TmSeq r ->
    result.bind (mapAccumLTypeOfH env r.tms) (lam t.
      match t with ((e, fv), [ty] ++ tys) then
        result.map
          (lam ty. { e = e, ty = ityseq_ r.info ty, fv = fv })
          (result.foldlM
             (lam ty1. lam ty2.
               optionMapOr
                 (result.err (DTCJoinError (r.info, Some (ty1, ty2))))
                 result.ok
                 (joinType (ty1, ty2)))
             ty tys)
      else error "impossible")
end

lang DTCTypeOfRecord = RecordAst + RecordTypeAst + DTCTypeOfBase
  sem typeOfH env =
  | TmRecord r ->
    match unzip (mapBindings r.bindings) with (sids, tms) in
    result.bind (mapAccumLTypeOfH env tms) (lam t.
      match t with ((e, fv), tys) in
      let ty = TyRecord {
        fields = mapFromSeq cmpSID (zip sids tys),
        info = r.info
      } in
      result.ok { e = e, ty = ty, fv = fv })
end

lang DTCPatTypeCheck = DTCTypeError
  sem dtcTypeCheckPat : DTCEnv -> Map Name Type -> (Type, Pat) ->
    Result DTCTypeError DTCTypeError (Map Name Type)
  sem dtcTypeCheckPat env patEnv =| (ty, pat) ->
    result.err (DTCPatError (infoPat pat, Some ty))

  sem dtcTypeCheckPatSeq : DTCEnv -> Map Name Type -> [(Type, Pat)] ->
    Result DTCTypeError DTCTypeError (Map Name Type)
  sem dtcTypeCheckPatSeq env patEnv =| ts ->
    result.foldlM
      (lam patEnv. lam t.
        match t with (ty, pat) in dtcTypeCheckPat env patEnv (ty, pat))
      patEnv ts
end

lang DTCTypeOfNever = NeverAst + DTCTypeOfBase
  sem typeOfH env =
  | TmNever r -> result.ok {
    e = ModD (), ty = TyBot { info = r.info }, fv = setEmpty nameCmp }
end

lang DTCTypeOfMatch = MatchAst + DTCPatTypeCheck + DTCTypeOfBase
  sem typeOfH env =
  | TmMatch (r & {els = TmNever _}) ->
    result.bind (typeOfHPromote env r.target) (lam target.
      result.bind
        (dtcTypeCheckPat env (mapEmpty nameCmp) (target.ty, r.pat))
        (lam patEnv.
          let thnEnv = dtcEnvBatchInsert patEnv env in
          result.bind2 (typeOfHPromote thnEnv r.thn) (typeOfHPromote env r.els)
            (lam thn. lam els.
              optionMapOr
                (result.err (DTCJoinError (r.info, Some (thn.ty, els.ty))))
                (lam ty.
                  resultOK [target.e, thn.e, els.e] ty [
                    target.fv,
                    setSubtract thn.fv (setOfKeys patEnv),
                    els.fv ])
                (joinType (thn.ty, els.ty)))))
  | TmMatch r -> typeOfBoolStrict env r

  -- NOTE(oerikss, 2025-10-14): We need stricter typing if it is possible that
  -- the match includes a condition on floating point values.
  sem typeOfBoolStrict env =
  | r ->
    result.bind (typeOfHPromote env r.target) (lam target.
      result.bind
        (dtcTypeCheckPat env (mapEmpty nameCmp) (target.ty, r.pat))
        (lam patEnv.
          let thnEnv = dtcEnvBatchInsert patEnv env in
          result.bind2 (typeOfHPromote thnEnv r.thn) (typeOfHPromote env r.els)
            (lam thn. lam els.
              if isFirstOrder thn.ty then
                if isFirstOrder els.ty then
                  optionMapOr
                    (result.err (DTCJoinError (r.info, Some (thn.ty, els.ty))))
                    (lam ty.
                      let tyP = setC (ModP ()) ty in
                      optionMapOr
                        (result.err (DTCJoinError (r.info, Some (tyP, ty))))
                        (lam ty.
                          resultOK [target.e, thn.e, els.e] ty [
                            target.fv,
                            setSubtract thn.fv (setOfKeys patEnv),
                            els.fv ])
                        (joinType (ty, tyP)))
                    (joinType (thn.ty, els.ty))
                else
                  result.err
                    (DTCHigherOrderTypeError (infoTm r.els, Some els.ty))
              else
                result.err
                  (DTCHigherOrderTypeError (infoTm r.thn, Some thn.ty)))))
end

lang DTCTypeOfInfer = Infer + DTCTypeOfBase
  sem typeOfH env =
  | TmInfer r ->
    result.bind2
      (inferSfold_Expr_Expr
         (foldTypeOfH env)
         (result.ok { e = ModD (), fv = setEmpty nameCmp }) r.method)
      (typeOfHPromote env r.model)
      (lam method. lam model.
        let err =
          argErr r.model
            (tyarrowce_ tyunit_ (tyvar_ "a") (ModM ()) (ModR ())) model.ty
        in
        match model with {ty = TyArrowCE (arr & {from = TyRecord rr})} then
          let ty = tyarrowce_ tyunit_ arr.to (ModM ()) (ModR ()) in
          if subtype (model.ty, ty) then
            if mapIsEmpty rr.fields then
              resultOK [method.e, model.e]
                (TyDist { info = r.info, ty = arr.to })
                [method.fv, model.fv]
            else argErr r.model ty model.ty
          else err
        else err)
end

lang DTCTypeOfAssume = Assume + DTCTypeOfBase
  sem typeOfH env =
  | TmAssume r ->
    result.bind (typeOfH env r.dist) (lam dist.
      match dist with {ty = TyDist distr} then
        let c = dtcEnvLubc (dtcEnvWeaken dist.fv env) in
        result.ok { dist with e = ModR (), ty = mulcType c distr.ty }
      else
        result.err
          (DTCArgError
            (infoTm r.dist, Some (tydist_ (tyvar_ "a"), dist.ty))))
end

lang DTCTypeOfObserve = Observe + DTCTypeOfBase
  sem typeOfH env =
  | TmObserve r ->
    result.bind2 (typeOfHPromote env r.value) (typeOfH env r.dist)
      (lam value. lam dist.
        match dist with {ty = TyDist {ty = suppTy}} then
          if subtype (value.ty, suppTy) then
            resultOK [value.e, dist.e] (tyWithInfo r.info tyunit_)
              [value.fv, dist.fv]
          else argErr r.value value.ty suppTy
        else argErr r.dist dist.ty (tydist_ value.ty))
end

lang DTCTypeOfWeight = Weight + DTCTypeOfBase
  sem typeOfH env =
  | TmWeight r ->
    result.bind (typeOfHPromote env r.weight) (lam weight.
      let ty = tyfloatc_ (ModM ()) in
      if subtype (weight.ty, ty) then
        result.ok {
          weight with e = ModR (), ty = tyWithInfo r.info tyunit_
        }
      else argErr r.weight weight.ty ty)
end

lang DTCTypeOfDist = Dist + WienerDist + DTCTypeOfBase
  sem typeOfH env =
  | TmDist r ->
    result.bind (mapAccumLTypeOfH env (distParams r.dist)) (lam t.
      match t with ((e, fv), tys) in
      match typeOfDist r.info r.dist with Some (paramTys, suppTy) then
        let params = distParams r.dist in
        result.bind
          (result.foldlM
             (lam. lam t.
               match t with (p, t) in
               if subtype t then result.ok ()
               else argErr p t.1 t.0)
             () (zip params (zip tys paramTys)))
          (lam. result.ok {
            e = e, ty = TyDist { ty = suppTy, info = r.info }, fv = fv
          })
      else result.err (DTCPolyDistError r.info))

  sem typeOfDist : Info -> Dist -> Option ([Type], Type)
  sem typeOfDist info =
  | DWiener r ->
    Some ( [tyunit_]
         , tyarrowce_ (tyfloatc_ (ModC ())) (tyfloatc_ (ModA ()))
             (ModM ()) (ModD ()) )
  | dist ->
    match distTy info dist with ([], paramTys, suppTy) then
      Some (map fromMExprTy paramTys, fromMExprTy suppTy)
    else None ()
end

lang IsIsomorficToRn = DTCFloatTypeAst + RecordTypeAst + SeqTypeAst

  -- Returns `true` if we can represent the type as a tuple of floats.
  sem isIsomorficToRn : Type -> Bool
  sem isIsomorficToRn =
  | TyFloatC _ -> true
  | ty & (TyRecord _ | TySeq _) ->
    sfold_Type_Type
      (lam acc. lam ty. and acc (isIsomorficToRn ty)) true ty
  | _ -> false
end

lang DTCTypeOfDiff = Diff + IsIsomorficToRn + DTCTypeOfBase
  sem typeOfH env =
  | TmDiff r ->
    result.bind3
      -- NOTE(oerikss, 2025-03-13): For practical reasons the syntax of `diff`
      -- differs slightly compared to the formalization. In the implementation
      -- we provide the argument to the total derivative directly in the `diff`
      -- term.
      (typeOfH env r.fn) (typeOfH env r.arg) (typeOfH env r.darg)
      (lam fn. lam arg. lam darg.
        match fn with {ty = TyArrowCE (arr & {e = ModD _})} then
          if and (isIsomorficToRn arr.from) (isIsomorficToRn arr.to)
          then
            let fnty = TyArrowCE { arr with c = ModP () } in
            if subtype (fn.ty, fnty) then
              let fv = foldl1 setUnion [fn.fv, arg.fv, darg.fv] in
              let promote = promote env fv in
              let tyO = lam c.
                if subtype (arg.ty, setC c arr.from) then
                  if subtype (darg.ty, setC (ModA ()) arr.from) then
                    resultOK [fn.e, arg.e, darg.e]
                      (promote (setC (ModA ()) arr.to)) [fv]
                  else argErr r.darg darg.ty arr.from
                else argErr r.arg arg.ty arr.from
              in
              if subtype (fn.ty, TyArrowCE {
                arr with
                from = setC (ModA ()) arr.from, to = setC (ModA ()) arr.to })
              then tyO (ModA ())
              else
                if subtype (fn.ty, TyArrowCE {
                  arr with
                  from = setC (ModP ()) arr.from, to = setC (ModA ()) arr.to })
                then tyO (ModP ())
                else
                  result.err (DTCDiffFnError (infoTm r.fn, Some (ModP (), fn.ty)))
            else result.err (DTCArgError (infoTm r.fn, Some (fnty, fn.ty)))
            else result.err (DTCDiffFnError (infoTm r.fn, Some (ModA (), fn.ty)))
        else result.err (DTCDiffFnError (infoTm r.fn, Some (ModP (), fn.ty))))
end

lang DTCTypeOfSolveODE = SolveODE + IsIsomorficToRn + DTCTypeOfBase
  sem typeOfH env =
  | TmSolveODE r ->
    result.bind4
      (sfold_ODESolverMetod_Expr
         (foldTypeOfH env)
         (result.ok { e = ModD (), fv = setEmpty nameCmp }) r.method)
      (typeOfH env r.model)
      (typeOfH env r.init)
      (typeOfH env r.endTime)
      (lam method. lam model. lam init. lam x1.
        match model.ty with
          TyArrowCE (arr1 & {
            from = TyFloatC {c = c & (ModA _ | ModC _)},
            to = TyArrowCE (arr2 & {e = ModD _}), e = ModD _})
        then
          if isIsomorficToRn arr2.from then
            let xTy = arr1.from in
            let yTy = setC (ModA ()) arr2.from in
            let odeRhsTy =
              TyArrowCE {
                arr1 with to = tyarrowce_ yTy yTy (ModA ()) (ModD ()),
                c = ModC ()
              }
            in
            let x1Ty = mulcType (ModPC ()) xTy in
            let fv =
              foldr1 setUnion [method.fv, model.fv, init.fv, x1.fv]
            in
            let promote = promote env fv in
            if subtype (model.ty, odeRhsTy) then
              if subtype (init.ty, tytuple_ [xTy, yTy]) then
                if subtype (x1.ty, x1Ty) then
                  resultOK [method.e, model.e, init.e, x1.e]
                    (promote (setC (ModA ()) (tytuple_ [xTy, yTy]))) [fv]
                else argErr r.endTime x1.ty x1Ty
              else
                argErr r.init init.ty (tytuple_ [xTy, yTy])
            else
              result.err
                (DTCArgError (infoTm r.model, Some (odeRhsTy, model.ty)))
          else
            result.err
              (DTCSolveODEModelError (infoTm r.model, Some model.ty))
        else
          result.err
            (DTCSolveODEModelError (infoTm r.model, Some model.ty)))
end

-- NOTE(oerikss, 2024-10-26): We only check that the subterms are well typed and
-- delegate type-checking of utest terms to the core PPL type-checker.
lang TypeOfUtest = UtestDeclAst + DTCTypeOfBase
  sem typeOfH env =
  | TmDecl (x & {decl = DeclUtest r}) ->
    result.bind
      (result.mapM
         (typeOfH env)
         (concat
            [r.test, r.expected]
            (map (optionGetOr unit_) [r.tusing, r.tonfail])))
      (lam. typeOfH env x.inexpr)
end

-- ┌───────────────────┐
-- │ Type of Constants │
-- └───────────────────┘

let iarr_ = lam info. lam from. lam to.
  use DTCAst in ityarrowe_ info from to (ModA ()) (ModD ())
let arr_ = lam from. lam to.
  use DTCAst in ityarrowe_ (NoInfo ()) from to (ModA ()) (ModD ())

lang DTCFloatType = DTCTyConst
  sem dtcConstType info =| CFloat _ -> result.ok (ityfloatc_ info (ModM ()))
end

-- NOTE(oerikss, 2025-10-08): We assume that elementary functions are analytic
-- and defined on the whole real number line. Evaluation at undefined inputs
-- will result in runtime errors.

lang DTCArithFloatType = ArithFloatAst + DTCTyConst
  sem dtcConstType info =
  | CAddf _ | CSubf _ | CMulf _ ->
    let tyfloata = ityfloatc_ info (ModA ()) in
    let arr = lam from. lam to. iarr_ info from to in
    result.ok (arr tyfloata (arr tyfloata tyfloata))
  | CDivf _ ->
      let tyfloata = lam c. ityfloatc_ info c in
      let arr = lam from. lam to. iarr_ info from to in
      result.ok
        (arr (tyfloata (ModA ()))
           (arr (tyfloata (ModP ())) (tyfloata (ModA ()))))
  | CNegf _ ->
    let tyfloata = ityfloatc_ info (ModA ()) in
    result.ok (iarr_ info tyfloata tyfloata)
end

lang DTCElementaryFunctionsType = ElementaryFunctions + DTCTyConst
  sem dtcConstType info =
  | CSin _ | CCos _ | CExp _ ->
    let tyfloata = ityfloatc_ info (ModA ()) in
    result.ok (iarr_ info tyfloata tyfloata)
   | CLog _ | CSqrt _  | CAbsf _ ->
    let tyfloata = ityfloatc_ info (ModPC ()) in
    result.ok (iarr_ info tyfloata tyfloata)
  | CPow _ ->
    let tyfloata = ityfloatc_ info (ModA ()) in
    let arr = lam from. lam to. iarr_ info from to in
    result.ok (arr tyfloata (arr tyfloata tyfloata))
end

lang DTCCmpFloatAstType = CmpFloatAst + DTCTyConst
  sem dtcConstType info =
  | CEqf _ | CLtf _ | CLeqf _ | CGtf _ | CGeqf _ | CNeqf _ ->
    let tyfloatp = ityfloatc_ info (ModP ()) in
    let arr = lam from. lam to. iarr_ info from to in
    result.ok (arr tyfloatp (arr tyfloatp (itybool_ info)))
end

let _a = tyvar_ "a"
let _b = tyvar_ "b"

lang DTCSysType = SysAst + DTCTypeOfConst
  sem dtcConstType info =
  | CExit _ -> result.ok (TyBot { info = info })
  | CError _ ->
    result.ok (iarr_ info (itystr_ info) (TyBot { info = info }))
end

lang DTCSeqOpType = SeqOpAst + DTCTypeOfConst
  sem _seqargerr tm =| ty ->
    result.err (DTCArgError (infoTm tm, Some (tyseq_ _a, ty)))

  -- NOTE(oerikss, 2024-10-21): We can handle polymorphic sequence operations if
  -- they are applied to enough arguments.
  sem typeOfH env =
  | TmApp (r & {lhs = TmConst {val = CSet _}}) ->
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      match rhs with {ty = TySeq seqr} then
        result.ok {
          rhs with
          ty =
            foldr1 (iarr_ r.info) [ityint_ r.info, seqr.ty, rhs.ty]
        }
      else _seqargerr r.rhs rhs.ty)
  | TmApp (r & {lhs = TmConst {val = CGet _}}) ->
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      match rhs with {ty = TySeq seqr} then
        result.ok { rhs with ty = iarr_ r.info (ityint_ r.info) seqr.ty }
      else _seqargerr r.rhs rhs.ty)
  | TmApp (r & {lhs = TmConst {val = CCons _}}) ->
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      let seq = ityseq_ r.info rhs.ty in
      result.ok { rhs with ty = iarr_ r.info seq seq })
  | TmApp (r & {lhs = TmConst {val = CSnoc _}}) ->
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      match rhs with {ty = TySeq seqr} then
        result.ok { rhs with ty = iarr_ r.info seqr.ty rhs.ty }
      else _seqargerr r.rhs rhs.ty)
  | TmApp (r & {lhs = TmConst {val = CConcat _ }}) ->
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      match rhs with {ty = TySeq _} then
        result.ok { rhs with ty = iarr_ r.info rhs.ty rhs.ty }
      else  _seqargerr r.rhs rhs.ty)
  | TmApp (r & {lhs = TmConst {val = CLength _}}) ->
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      match rhs with {ty = TySeq _} then
        result.ok { rhs with ty = ityint_ r.info }
      else _seqargerr r.rhs rhs.ty)
  | TmApp (r & {lhs = TmConst {val = CHead _}}) ->
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      match rhs with {ty = TySeq seqr} then
        result.ok { rhs with ty = seqr.ty }
      else _seqargerr r.rhs rhs.ty)
  | TmApp (r & {lhs = TmConst {val = CTail _ | CReverse _}}) ->
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      match rhs with {ty = TySeq _} then
        result.ok { rhs with ty = rhs.ty }
      else _seqargerr r.rhs rhs.ty)
  | TmApp (r & {lhs = TmConst {val = CNull _ | CIsList _ | CIsRope _}}) ->
    result.bind (typeOfH env r.rhs) (lam rhs.
      match rhs with {ty = TySeq _} then
        result.ok { rhs with ty = itybool_ r.info }
      else _seqargerr r.rhs rhs.ty)
  | TmApp (r & {lhs = TmConst {val = CMap _}}) ->
    -- NOTE(oerikss, 2025-10-01): See notes on general application.
    result.bind (typeOfH env r.rhs) (lam rhs.
      match rhs with {ty = TyArrowCE arr} then
        let seq = ityseq_ r.info in
        result.ok {
          rhs with
          ty = ityarrowe_ r.info (seq arr.from) (seq arr.to) (ModA ()) arr.e
        }
      else argErr r.rhs (arr_ _a _b) rhs.ty)
  | TmApp (r & {lhs = TmConst {val = CMapi _}}) ->
    -- NOTE(oerikss, 2025-10-01): See notes on general application.
    result.bind (typeOfH env r.rhs) (lam rhs.
      match rhs with
        { ty = TyArrowCE (arr1 & {from = TyInt _, to = TyArrowCE arr2}) }
      then
        let seq = ityseq_ r.info in
        result.ok {
          rhs with
          ty = ityarrowe_ r.info (seq arr2.from) (seq arr2.to)
                 (ModA ())
                 (dtcMule arr1.e arr2.e)
        }
      else argErr r.rhs (foldr1 arr_ [tyint_, _a, _b]) rhs.ty)
  | TmApp (r & {lhs = TmConst {val = CIter _}}) ->
    -- NOTE(oerikss, 2025-10-01): See notes on general application.
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      let err = argErr r.rhs (arr_ _a tyunit_) rhs.ty in
      match rhs with {ty = TyArrowCE (arr & {to = TyRecord rr})} then
        if mapIsEmpty rr.fields then
          result.ok {
          rhs with
          ty = ityarrowe_ r.info (ityseq_ r.info arr.from) arr.to (ModA ()) arr.e
        }
        else err
      else err)
  | TmApp (r & {lhs = TmConst {val = CIteri _}}) ->
    -- NOTE(oerikss, 2025-10-01): See notes on general application.
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      let err = argErr r.rhs (foldr1 arr_ [tyint_, _a, tyunit_]) rhs.ty in
      match rhs with
        { ty = TyArrowCE (arr1 & {
          from = TyInt _, to = TyArrowCE (arr2 & {
            to = TyRecord rr})}) }
      then
        if mapIsEmpty rr.fields then
          let seq = ityseq_ r.info in
          result.ok {
            rhs with
            ty = ityarrowe_ r.info (seq arr2.from) arr2.to
                   (ModA ())
                   (dtcMule arr1.e arr2.e)
          }
        else err
      else err)
  | TmApp (r & {lhs = TmConst {val = CFoldl _}}) ->
    -- NOTE(oerikss, 2025-10-01): See notes on general application.
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      let err = argErr r.rhs (foldr1 arr_ [_a, _b, _a]) rhs.ty in
      match rhs with { ty = TyArrowCE (arr1 & {to = TyArrowCE arr2}) } then
        optionMapOr err
          (lam ty.
            let arr = lam from. lam to. ityarrowe_ r.info from to (ModA ()) in
            result.ok {
              rhs with
              ty =
                arr
                  ty
                  (arr (ityseq_ r.info arr2.from) ty (dtcMule arr1.e arr2.e))
                  (ModD ())
            })
          (joinType (arr1.from, arr2.to))
      else err)
  | TmApp (r & {lhs = TmConst {val = CFoldr _}}) ->
    -- NOTE(oerikss, 2025-10-01): See notes on general application.
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      let err = argErr r.rhs (foldr1 arr_ [_a, _b, _b]) rhs.ty in
      match rhs with { ty = TyArrowCE (arr1 & {to = TyArrowCE arr2}) } then
        optionMapOr err
          (lam ty.
            let arr = lam from. lam to. ityarrowe_ r.info from to (ModA ()) in
            result.ok {
              rhs with
              ty =
                arr
                  ty
                  (arr (ityseq_ r.info arr1.from) ty (dtcMule arr1.e arr2.e))
                  (ModD ())
            })
          (joinType (arr2.from, arr2.to))
      else err)
  | TmApp (r2 & {lhs = TmApp (r1 & {
    lhs = TmConst {val = CCreate _ | CCreateList _ | CCreateRope _}})}) ->
    result.bind2 (typeOfH env r1.rhs) (typeOfH env r2.rhs) (lam rhs1. lam rhs2.
      match rhs1.ty with TyInt _ then
        -- NOTE(oerikss, 2025-10-01): See notes on general application.
        match rhs2.ty with TyArrowCE (arr & {from = TyInt _}) then
          resultOK [rhs1.e, arr.e] (ityseq_ r2.info arr.to) [rhs1.fv, rhs2.fv]
        else argErr r2.rhs (arr_ tyint_ _a) rhs2.ty
      else argErr r1.rhs tyint_ rhs1.ty)
  | TmApp (r & {lhs = TmConst {val = CSplitAt _}}) ->
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      match rhs with {ty = TySeq _} then
        result.ok {
          rhs with
          ty = iarr_ r.info (ityint_ r.info)
                 (itytuple_ r.info [rhs.ty, rhs.ty])
        }
      else _seqargerr r.rhs r.ty)
  | TmApp (r & {lhs = TmConst {val = CSubsequence _}}) ->
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      let int = ityint_ r.info in
      match rhs with {ty = TySeq _} then
        result.ok { rhs with ty = foldr1 (iarr_ r.info) [int, int, rhs.ty] }
      else _seqargerr r.rhs r.ty)
end

lang DTCDistOpType = Dist + DTCTypeOfConst
  -- Type-checks polymorfic constant functions over distributions

  sem _distargerr tm =| ty ->
    result.err (DTCArgError (infoTm tm, Some (tydist_ _a, ty)))

  sem typeOfH env =
  | TmApp (r & {lhs = TmConst {val = CDistEmpiricalSamples _}}) ->
    result.bind (typeOfH env r.rhs) (lam rhs.
      match rhs with {ty = TyDist distr} then
        let seq = ityseq_ r.info in
        result.ok {
          rhs with ty = itytuple_ r.info [
            seq distr.ty, seq (ityfloatc_ r.info (ModM ()))]
        }
      else _distargerr r.rhs rhs.ty)
  | TmApp (r & {lhs = TmConst {val = CDistEmpiricalDegenerate _}}) ->
    result.bind (typeOfH env r.rhs) (lam rhs.
      match rhs with {ty = TyDist _} then
        result.ok { rhs with ty = itybool_ r.info }
      else _distargerr r.rhs rhs.ty)
  | TmApp (r & {lhs = TmConst {
    val = CDistEmpiricalNormConst _ | CDistEmpiricalAcceptRate _ }}) ->
    result.bind (typeOfH env r.rhs) (lam rhs.
      match rhs with {ty = TyDist _} then
        result.ok { rhs with ty = ityfloatc_ r.info (ModM ()) }
      else _distargerr r.rhs rhs.ty)
end

-- ┌─────────────────────┐
-- │ Type Check Patterns │
-- └─────────────────────┘

lang DTCPatTypeCheckAll =
  NamedPat + SeqTotPat + SeqEdgePat + RecordPat + IntPat + CharPat + BoolPat +
  AndPat + OrPat + NotPat +
  SeqTypeAst + UnknownTypeAst + RecordTypeAst + IntTypeAst + CharTypeAst +
  BoolTypeAst +
  DTCPatTypeCheck + DTCAstBase

  -- TODO(oerikss, 2024-10-16): This language fragment could be broken into one
  -- fragment for each pattern constructor. However, the benefit of implementing
  -- all patterns in the same fragment is that they can re-use more code.

  sem ipatNamed_ i =| ident -> PatNamed {
    ident = ident,
    info = i,
    ty = TyUnknown { info = i }}

  sem dtcTypeCheckPat env patEnv =
  | (patTy, PatNamed (r & {ident = PName ident})) ->
    optionMapOrElse
      (lam. result.ok (mapInsert ident patTy patEnv))
      (lam ty.
        optionMapOr (result.err (DTCJoinError (r.info, Some (patTy, ty))))
          (lam ty. result.ok (mapInsert ident ty patEnv))
          (joinType (patTy, ty)))
      (mapLookup ident patEnv)
  | (_, PatNamed {ident = PWildcard _}) -> result.ok patEnv
  | (TySeq tr, PatSeqTot pr) ->
    dtcTypeCheckPatSeq env patEnv (map (lam pat. (tr.ty, pat)) pr.pats)
  | (ty & TySeq _, PatSeqEdge pr) ->
    let patSeqTot = lam pats.
      PatSeqTot { pats = pats, info = pr.info, ty = pr.ty }
    in
    result.bind
      (dtcTypeCheckPat env patEnv (ty, patSeqTot pr.prefix))
      (lam patEnv.
        result.bind
          (dtcTypeCheckPat env patEnv (ty, ipatNamed_ pr.info pr.middle))
          (lam patEnv.
            dtcTypeCheckPat env patEnv (ty, patSeqTot pr.postfix)))
  | (TyRecord tr, PatRecord pr) ->
    let m =
      mapMerge
        (lam ty. lam pat.
          switch (ty, pat)
          case (_, None _) then None ()
          case (None _, Some pat) then
            Some (result.err (DTCPatError (pr.info, Some (TyRecord tr))))
          case (Some ty, Some pat) then Some (result.ok (ty, pat))
          end)
        tr.fields pr.bindings
    in
    result.bind (result.mapM (lam x. x) (mapValues m))
      (dtcTypeCheckPatSeq env patEnv)
  | (TyInt _, PatInt _) | (TyChar _, PatChar _) | (TyBool _, PatBool _) ->
    result.ok patEnv
  | (ty, pat & (PatAnd _ | PatOr _ | PatNot _)) ->
    sfold_Pat_Pat
      (lam patEnv. lam pat.
        result.bind patEnv
          (lam patEnv. dtcTypeCheckPat env patEnv (ty, pat)))
      (result.ok patEnv) pat
end

lang DTCTypeOf =
  -- Terms
  DTCTypeOfVar + DTCTypeOfLam + DTCTypeOfApp + DTCTypeOfLet + DTCTypeOfConst +
  DTCTypeOfSeq + DTCTypeOfRecord + DTCTypeOfNever + DTCTypeOfMatch +
  DTCTypeOfInfer + DTCTypeOfAssume + DTCTypeOfObserve + DTCTypeOfWeight +
  DTCTypeOfDist + DTCTypeOfDiff + DTCTypeOfSolveODE + TypeOfUtest +

  -- Constants
  DTCTyConst + DTCFloatType + DTCArithFloatType + DTCElementaryFunctionsType +
  DTCCmpFloatAstType + DTCSysType + DTCSeqOpType + DTCDistOpType +

  -- Patterns
  DTCPatTypeCheckAll
end

lang TestLang = DTCTypeOf + MExprPPL end

mexpr

use TestLang in

-- Define some shorthand names.

let _D  = ModD () in
let _R  = ModR () in
let _A  = ModA () in
let _PC = ModPC () in
let _P  = ModP () in
let _C  = ModC () in
let _M  = ModM () in

let _x = nameNoSym "x" in
let _y = nameNoSym "y" in
let _z = nameNoSym "z" in
let _u = nameNoSym "u" in
let _v = nameNoSym "v" in
let _w = nameNoSym "w" in
let _f = nameNoSym "f" in
let _g = nameNoSym "g" in
let _h = nameNoSym "h" in

let alltypes = [
  tyfloatc_ _A, tyfloatc_ _P, tyfloatc_ _M,
  tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _A _D,
  tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _A _R,
  tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _PC _D,
  tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _PC _R,
  tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _P _D,
  tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _P _R,
  tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _C _D,
  tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _C _R,
  tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _M _D,
  tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _M _R,
  tytuple_ [tyfloatc_ _A, tyfloatc_ _P, tyfloatc_ _C, tyfloatc_ _M],
  tyseq_ (tyfloatc_ _A),
  tyint_,
  tybool_,
  tydist_ (tyfloatc_ _A)
] in

-- ┌───────────────────────────┐
-- │ Test eraseDecorationsType │
-- └───────────────────────────┘

utest eraseDecorationsType (tyfloatc_ _A) with tyfloat_ using eqType in
utest
  eraseDecorationsType
    (tyarrowce_
       (tyfloatc_ _A)
       (tyarrowce_ (tychar_) (tyfloatc_ _A) _A _D)
      _A _D)
  with tyarrow_ tyfloat_ (tyarrow_ tychar_ tyfloat_) using eqType
in

-- ┌───────────────┐
-- │ Test leqcType │
-- └───────────────┘

utest leqcType _A (tyfloatc_ _A) with true in
utest leqcType _A (tyfloatc_ _P) with false in
utest leqcType _P (tyfloatc_ _A) with true in
let rhs = tytuple_ [
  tyfloatc_ _P,
  tyseq_ (tyfloatc_ _M),
  tytuple_ [tyfloatc_ _C],
  tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _A _D
] in
utest leqcType _A rhs with false in
utest leqcType _PC rhs with false in
utest leqcType _P rhs with false in
utest leqcType _C rhs with false in
utest leqcType _M rhs with true in

-- ┌──────────────┐
-- │ Test eqcType │
-- └──────────────┘

utest eqcType _A (tyfloatc_ _A) with true in
utest eqcType _A (tyfloatc_ _P) with false in
utest eqcType _P (tyfloatc_ _A) with false in
let rhs = tytuple_ [
  tyfloatc_ _P,
  tytuple_ [tyfloatc_ _C],
  tyseq_ (tyfloatc_ _M),
  tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _A _D
] in
utest eqcType _A rhs with false in
utest eqcType _PC rhs with false in
utest eqcType _P rhs with false in
utest eqcType _C rhs with false in
utest eqcType _M rhs with false in
let rhs = lam c. tytuple_ [
  tyfloatc_ c,
  tyseq_ (tyfloatc_ c)
] in
utest eqcType _A (rhs _A) with true in
utest eqcType _P (rhs _A) with false in
utest eqcType _PC (rhs _PC) with true in
utest eqcType _C (rhs _A) with false in
utest eqcType _M (rhs _A) with false in
utest eqcType _A (rhs _P) with false in
utest eqcType _P (rhs _P) with true in
utest eqcType _C (rhs _P) with false in
utest eqcType _M (rhs _P) with false in
let rhs = tytuple_ [
  tyfloatc_ _M,
  tyseq_ (tyfloatc_ _M),
  tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _M _D
] in
utest eqcType _A rhs with false in
utest eqcType _PC rhs with false in
utest eqcType _P rhs with false in
utest eqcType _C rhs with false in
utest eqcType _M rhs with true in

-- ┌───────────────┐
-- │ Test leqTypec │
-- └───────────────┘

utest leqTypec (tyfloatc_ _A) _A with true in
utest leqTypec (tyfloatc_ _P) _A with true in
utest leqTypec (tyfloatc_ _A) _P with false in
let rhs = tytuple_ [
  tyfloatc_ _P,
  tytuple_ [tyfloatc_ _C],
  tyseq_ (tyfloatc_ _M),
  tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _P _D
] in
utest leqTypec rhs _A with true in
utest leqTypec rhs _PC with true in
utest leqTypec rhs _P with false in
utest leqTypec rhs _C with false in
utest leqTypec rhs _M with false in

-- ┌─────────────────┐
-- │ Test dtcLeqcEnv │
-- └─────────────────┘

utest dtcLeqcEnv _A (dtcEnvOfSeq []) with true in
utest dtcLeqcEnv _A (dtcEnvOfSeq [(_x, tyfloatc_ _A)]) with true in
let env = dtcEnvOfSeq [(_x, tyfloatc_ _P), (_y, tyfloatc_ _M)] in
utest dtcLeqcEnv _A env with false in
utest dtcLeqcEnv _PC env with false in
utest dtcLeqcEnv _P env with false in
utest dtcLeqcEnv _M env with true in
utest
  dtcLeqcEnv _M
    (dtcEnvOfSeq [(_x, (tyarrowce_ (tychar_) (tyfloatc_ _A) _A _D))])
  with true
in

-- ┌───────────────┐
-- │ Test mulcType │
-- └───────────────┘

utest mulcType _A (tyfloatc_ _A) with tyfloatc_ _A using eqType in
utest mulcType _A (tyfloatc_ _P) with tyfloatc_ _P using eqType in
utest mulcType _P (tyfloatc_ _A) with tyfloatc_ _P using eqType in
utest mulcType _C (tyfloatc_ _P) with tyfloatc_ _M using eqType in
utest mulcType _P (tyfloatc_ _C) with tyfloatc_ _M using eqType in
utest mulcType _M (tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _A _D) with
  tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _M _D using eqType
in
utest mulcType _P (tytuple_ [tyfloatc_ _A, tyfloatc_ _M]) with
  tytuple_ [tyfloatc_ _P, tyfloatc_ _M] using eqType
in
utest mulcType _P (tyseq_ (tyfloatc_ _A))
  with (tyseq_ (tyfloatc_ _P)) using eqType
in
utest mulcType _P (tydist_ (tyfloatc_ _A))
  with (tydist_ (tyfloatc_ _A)) using eqType
in

-- ┌──────────────┐
-- │ Test subtype │
-- └──────────────┘

-- Bottom type
utest
  forAll (lam ty. and (subtype (tybot_, ty)) (not (subtype (ty, tybot_))))
    alltypes
  with true
in

-- Float
let _subtype = lam c1. lam c2.
  subtype (tyfloatc_ c1, tyfloatc_ c2)
in

utest _subtype _A _A with true in
utest _subtype _A _PC with false in
utest _subtype _A _P with false in
utest _subtype _A _C with false in
utest _subtype _A _M with false in

utest _subtype _PC _A with true in
utest _subtype _PC _PC with true in
utest _subtype _PC _P with false in
utest _subtype _PC _C with false in
utest _subtype _PC _M with false in

utest _subtype _P _A with true in
utest _subtype _P _PC with true in
utest _subtype _P _P with true in
utest _subtype _P _C with false in
utest _subtype _P _M with false in

utest _subtype _C _A with true in
utest _subtype _C _PC with true in
utest _subtype _C _P with false in
utest _subtype _C _C with true in
utest _subtype _C _M with false in

utest _subtype _M _A with true in
utest _subtype _M _PC with true in
utest _subtype _M _P with true in
utest _subtype _M _C with true in
utest _subtype _M _M with true in

utest subtype (tyfloatc_ _A, tytuple_ [tyfloatc_ _A]) with false in

-- Sequences
utest subtype (tyseq_ (tyfloatc_ _P), tyseq_ (tyfloatc_ _A)) with true in

-- Records
let tup2 = lam c1. lam c2. tytuple_ [tyfloatc_ c1, tyfloatc_ c2] in
let tup3 = lam c1. lam c2. lam c3.
  tytuple_ [tyfloatc_ c1, tyfloatc_ c2, tyfloatc_ c2]
in

utest subtype (tup2 _A _A, tup2 _A _A) with true in
utest subtype (tup2 _A _A, tup3 _A _A _A) with false in
utest subtype (tup3 _A _A _A, tup2 _A _A) with false in
utest subtype (tup2 _P _M, tup2 _A _P) with true in
utest subtype (tup2 _A _A, tup2 _A _P) with false in

-- Arrows
let arr = lam c1. lam c2. lam e.
  tyarrowce_ (tyfloatc_ c1) (tyfloatc_ c2) _A e
in

utest subtype (arr _A _A _D, arr _A _A _D) with true in
utest subtype (arr _A _A _D, arr _A _A _R) with true in
utest subtype (arr _A _A _R, arr _A _A _R) with true in
utest subtype (arr _A _A _R, arr _A _A _D) with false in
utest subtype (arr _A _P _D, arr _A _A _D) with true in
utest subtype (arr _A _A _D, arr _P _A _D) with true in

let arr = lam c.
  tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) c _D
in

utest subtype (arr _A, arr _A) with true in
utest subtype (arr _PC, arr _A) with true in
utest subtype (arr _P, arr _A) with true in
utest subtype (arr _C, arr _A) with true in
utest subtype (arr _M, arr _A) with true in

utest subtype (arr _A, arr _PC) with false in
utest subtype (arr _PC, arr _PC) with true in
utest subtype (arr _P, arr _PC) with true in
utest subtype (arr _C, arr _PC) with true in
utest subtype (arr _M, arr _PC) with true in

utest subtype (arr _A, arr _P) with false in
utest subtype (arr _PC, arr _P) with false in
utest subtype (arr _P, arr _P) with true in
utest subtype (arr _C, arr _P) with false in
utest subtype (arr _M, arr _P) with true in

utest subtype (arr _A, arr _C) with false in
utest subtype (arr _PC, arr _C) with false in
utest subtype (arr _P, arr _C) with false in
utest subtype (arr _C, arr _C) with true in
utest subtype (arr _M, arr _C) with true in

utest subtype (arr _A, arr _M) with false in
utest subtype (arr _PC, arr _M) with false in
utest subtype (arr _P, arr _M) with false in
utest subtype (arr _C, arr _M) with false in
utest subtype (arr _M, arr _M) with true in

-- Type variables
utest subtype (tyvar_ "X", tyvar_ "X") with true in
utest subtype (tyvar_ "X", tyvar_ "Y") with false in

-- Distributions
let dist = lam c. tydist_ (tyfloatc_ c) in

utest subtype (dist _A, dist _A) with true in
utest subtype (dist _A, dist _P) with false in

-- ┌────────────────────────┐
-- │ Test joinType/meetType │
-- └────────────────────────┘

let eq = optionEq eqType in

-- Bottom type
utest
  forAll (lam ty.
    and
      (eq (joinType (ty, tybot_)) (Some ty))
      (eq (joinType (tybot_, ty)) (Some ty)))
    alltypes
  with true
in

utest meetType (tybot_, tybot_) with (Some tybot_) using eq in

-- Base types
let _joinType = lam c1. lam c2. joinType (tyfloatc_ c1, tyfloatc_ c2) in

utest _joinType _A _A  with Some (tyfloatc_ _A)  using eq in
utest _joinType _A _PC with Some (tyfloatc_ _A)  using eq in
utest _joinType _PC _A with Some (tyfloatc_ _A)  using eq in
utest _joinType _A _P  with Some (tyfloatc_ _A)  using eq in
utest _joinType _P _A  with Some (tyfloatc_ _A)  using eq in
utest _joinType _C _A  with Some (tyfloatc_ _A)  using eq in
utest _joinType _A _C  with Some (tyfloatc_ _A)  using eq in
utest _joinType _A _M  with Some (tyfloatc_ _A)  using eq in
utest _joinType _M _A  with Some (tyfloatc_ _A)  using eq in
utest _joinType _PC _P with Some (tyfloatc_ _PC) using eq in
utest _joinType _P _PC with Some (tyfloatc_ _PC) using eq in
utest _joinType _PC _C with Some (tyfloatc_ _PC) using eq in
utest _joinType _C _PC with Some (tyfloatc_ _PC) using eq in
utest _joinType _PC _M with Some (tyfloatc_ _PC) using eq in
utest _joinType _M _PC with Some (tyfloatc_ _PC) using eq in
utest _joinType _P _P  with Some (tyfloatc_ _P)  using eq in
utest _joinType _P _C  with Some (tyfloatc_ _PC) using eq in
utest _joinType _C _P  with Some (tyfloatc_ _PC) using eq in
utest _joinType _P _M  with Some (tyfloatc_ _P)  using eq in
utest _joinType _M _P  with Some (tyfloatc_ _P)  using eq in
utest _joinType _C _C  with Some (tyfloatc_ _C)  using eq in
utest _joinType _C _M  with Some (tyfloatc_ _C)  using eq in
utest _joinType _M _C  with Some (tyfloatc_ _C)  using eq in
utest _joinType _M _M  with Some (tyfloatc_ _M)  using eq in

let _meetType = lam c1. lam c2. meetType (tyfloatc_ c1, tyfloatc_ c2) in

utest _meetType _A _A  with Some (tyfloatc_ _A)  using eq in
utest _meetType _A _PC with Some (tyfloatc_ _PC) using eq in
utest _meetType _PC _A with Some (tyfloatc_ _PC) using eq in
utest _meetType _A _P  with Some (tyfloatc_ _P)  using eq in
utest _meetType _P _A  with Some (tyfloatc_ _P)  using eq in
utest _meetType _C _A  with Some (tyfloatc_ _C)  using eq in
utest _meetType _A _C  with Some (tyfloatc_ _C)  using eq in
utest _meetType _A _M  with Some (tyfloatc_ _M)  using eq in
utest _meetType _M _A  with Some (tyfloatc_ _M)  using eq in
utest _meetType _PC _P with Some (tyfloatc_ _P)  using eq in
utest _meetType _P _PC with Some (tyfloatc_ _P)  using eq in
utest _meetType _PC _C with Some (tyfloatc_ _C)  using eq in
utest _meetType _C _PC with Some (tyfloatc_ _C)  using eq in
utest _meetType _PC _M with Some (tyfloatc_ _M)  using eq in
utest _meetType _M _PC with Some (tyfloatc_ _M)  using eq in
utest _meetType _P _P  with Some (tyfloatc_ _P)  using eq in
utest _meetType _P _C  with Some (tyfloatc_ _M) using eq in
utest _meetType _C _P  with Some (tyfloatc_ _M) using eq in
utest _meetType _P _M  with Some (tyfloatc_ _M)  using eq in
utest _meetType _M _P  with Some (tyfloatc_ _M)  using eq in
utest _meetType _C _C  with Some (tyfloatc_ _C)  using eq in
utest _meetType _C _M  with Some (tyfloatc_ _M)  using eq in
utest _meetType _M _C  with Some (tyfloatc_ _M)  using eq in
utest _meetType _M _M  with Some (tyfloatc_ _M)  using eq in

-- Sequences
let seq = lam c. tyseq_ (tyfloatc_ c) in

utest joinType (seq _A, seq _A) with Some (seq _A) using eq in
utest joinType (seq _A, seq _P) with Some (seq _A) using eq in
utest joinType (seq _P, seq _A) with Some (seq _A) using eq in
utest joinType (seq _P, seq _P) with Some (seq _P) using eq in
utest meetType (seq _A, seq _A) with Some (seq _A) using eq in
utest meetType (seq _A, seq _P) with Some (seq _P) using eq in
utest meetType (seq _P, seq _A) with Some (seq _P) using eq in
utest meetType (seq _P, seq _P) with Some (seq _P) using eq in
utest meetType (seq _P, tyfloatc_ _A) with None () using eq in

-- Records
utest joinType (tup2 _A _A, tup2 _A _A) with Some (tup2 _A _A) using eq in
utest joinType (tup2 _A _A, tup3 _A _A _A) with None () using eq in
utest joinType (tup3 _A _A _A, tup2 _A _A) with None () using eq in
utest joinType (tup2 _P _M, tup2 _A _P) with Some (tup2 _A _P) using eq in
utest joinType (tup2 _A _A, tup2 _A _P) with Some (tup2 _A _A) using eq in

utest meetType (tup2 _A _A, tup2 _A _A) with Some (tup2 _A _A) using eq in
utest meetType (tup2 _A _A, tup3 _A _A _A) with None () using eq in
utest meetType (tup3 _A _A _A, tup2 _A _A) with None () using eq in
utest meetType (tup2 _P _M, tup2 _A _P) with Some (tup2 _P _M) using eq in
utest meetType (tup2 _A _A, tup2 _A _P) with Some (tup2 _A _P) using eq in

-- Arrows
let arr = tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _A in
let _joinType = lam e1. lam e2. joinType (arr e1, arr e2) in

utest _joinType _D _D with Some (arr _D) using eq in
utest _joinType _D _R with Some (arr _R) using eq in
utest _joinType _R _D with Some (arr _R) using eq in
utest _joinType _R _R with Some (arr _R) using eq in

let _meetType = lam e1. lam e2. meetType (arr e1, arr e2) in

utest _meetType _D _D with Some (arr _D) using eq in
utest _meetType _D _R with Some (arr _D) using eq in
utest _meetType _R _D with Some (arr _D) using eq in
utest _meetType _R _R with Some (arr _R) using eq in

let arr = lam c. tyarrowce_ (tyfloatc_ c) (tyfloatc_ _A) _A _D in
let _joinType = lam c1. lam c2. joinType (arr c1, arr c2) in

utest _joinType _A _A with Some (arr _A) using eq in
utest _joinType _A _P with Some (arr _P) using eq in
utest _joinType _P _A with Some (arr _P) using eq in

let _meetType = lam c1. lam c2. meetType (arr c1, arr c2) in

utest _meetType _A _A with Some (arr _A) using eq in
utest _meetType _A _P with Some (arr _A) using eq in
utest _meetType _P _A with Some (arr _A) using eq in

let arr = lam c. tyarrowce_ (tyfloatc_ _A) (tyfloatc_ c) _A _D in
let _joinType = lam c1. lam c2. joinType (arr c1, arr c2) in

utest _joinType _A _A with Some (arr _A) using eq in
utest _joinType _A _P with Some (arr _A) using eq in
utest _joinType _P _A with Some (arr _A) using eq in

let _meetType = lam c1. lam c2. meetType (arr c1, arr c2) in

utest _meetType _A _A with Some (arr _A) using eq in
utest _meetType _A _P with Some (arr _P) using eq in
utest _meetType _P _A with Some (arr _P) using eq in

let arr = lam c. tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) c _D in
let _joinType = lam c1. lam c2. joinType (arr c1, arr c2) in

utest _joinType _A _A   with Some (arr _A)  using eq in
utest _joinType _A _PC  with Some (arr _A)  using eq in
utest _joinType _PC _A  with Some (arr _A)  using eq in
utest _joinType _A _P   with Some (arr _A)  using eq in
utest _joinType _P _A   with Some (arr _A)  using eq in
utest _joinType _A _C   with Some (arr _A)  using eq in
utest _joinType _C _A   with Some (arr _A)  using eq in
utest _joinType _A _M   with Some (arr _A)  using eq in
utest _joinType _M _A   with Some (arr _A)  using eq in
utest _joinType _PC _PC with Some (arr _PC) using eq in
utest _joinType _PC _P  with Some (arr _PC) using eq in
utest _joinType _P _PC  with Some (arr _PC) using eq in
utest _joinType _PC _C  with Some (arr _PC) using eq in
utest _joinType _C _PC  with Some (arr _PC) using eq in
utest _joinType _PC _M  with Some (arr _PC) using eq in
utest _joinType _M _PC  with Some (arr _PC) using eq in
utest _joinType _P _P   with Some (arr _P)  using eq in
utest _joinType _P _C   with Some (arr _PC) using eq in
utest _joinType _C _P   with Some (arr _PC) using eq in
utest _joinType _P _M   with Some (arr _P)  using eq in
utest _joinType _M _P   with Some (arr _P)  using eq in
utest _joinType _C _C   with Some (arr _C)  using eq in
utest _joinType _C _M   with Some (arr _C)  using eq in
utest _joinType _M _C   with Some (arr _C)  using eq in
utest _joinType _M _M   with Some (arr _M)  using eq in

let _meetType = lam c1. lam c2. meetType (arr c1, arr c2) in

utest _meetType _A _A   with Some (arr _A)  using eq in
utest _meetType _A _PC  with Some (arr _PC) using eq in
utest _meetType _PC _A  with Some (arr _PC) using eq in
utest _meetType _A _P   with Some (arr _P)  using eq in
utest _meetType _P _A   with Some (arr _P)  using eq in
utest _meetType _A _C   with Some (arr _C)  using eq in
utest _meetType _C _A   with Some (arr _C)  using eq in
utest _meetType _A _M   with Some (arr _M)  using eq in
utest _meetType _M _A   with Some (arr _M)  using eq in
utest _meetType _PC _PC with Some (arr _PC) using eq in
utest _meetType _PC _P  with Some (arr _P)  using eq in
utest _meetType _P _PC  with Some (arr _P)  using eq in
utest _meetType _PC _C  with Some (arr _C)  using eq in
utest _meetType _C _PC  with Some (arr _C)  using eq in
utest _meetType _PC _M  with Some (arr _M)  using eq in
utest _meetType _M _PC  with Some (arr _M)  using eq in
utest _meetType _P _P   with Some (arr _P)  using eq in
utest _meetType _P _C   with Some (arr _M)  using eq in
utest _meetType _C _P   with Some (arr _M)  using eq in
utest _meetType _P _M   with Some (arr _M)  using eq in
utest _meetType _M _P   with Some (arr _M)  using eq in
utest _meetType _C _C   with Some (arr _C)  using eq in
utest _meetType _C _M   with Some (arr _M)  using eq in
utest _meetType _M _C   with Some (arr _M)  using eq in
utest _meetType _M _M   with Some (arr _M)  using eq in

-- Type variables
utest joinType (tyvar_ "X", tyvar_ "X") with Some (tyvar_ "X") using eq in
utest joinType (tyvar_ "X", tyvar_ "Y") with None () using eq in
utest meetType (tyvar_ "X", tyvar_ "X") with Some (tyvar_ "X") using eq in
utest meetType (tyvar_ "X", tyvar_ "Y") with None () using eq in

-- Distributions
let dist = lam c. tydist_ (tyfloatc_ c) in

utest joinType (dist _A, dist _A) with Some (dist _A) using eq in
utest joinType (dist _A, dist _P) with Some (dist _A) using eq in
utest joinType (dist _P, dist _A) with Some (dist _A) using eq in

utest meetType (dist _A, dist _A) with Some (dist _A) using eq in
utest meetType (dist _A, dist _P) with Some (dist _P) using eq in
utest meetType (dist _P, dist _A) with Some (dist _P) using eq in

-- ┌───────────────┐
-- │ Test glbcType │
-- └───────────────┘

-- Bottom
utest glbcType tybot_ with _A in

-- Float
let _glbcType = lam c. glbcType (tyfloatc_ c) in

utest _glbcType _A with _A in
utest _glbcType _M with _M in

-- Seqences
let _glbcType = lam c. glbcType (tyseq_ (tyfloatc_ c)) in

utest _glbcType _A with _A in
utest _glbcType _M with _M in

-- Records
let _glbcType = lam c1. lam c2. glbcType (tytuple_ [tyfloatc_ c1, tyfloatc_ c2]) in

utest _glbcType _A _A with _A in
utest _glbcType _A _P with _P in
utest _glbcType _P _A with _P in

-- Arrows
let _glbcType = lam c1. lam c2.
  glbcType (tyarrowce_ (tyfloatc_ c1) (tyfloatc_ c2) _A _D)
in

utest _glbcType _A _A with _A in
utest _glbcType _A _P with _A in
utest _glbcType _P _A with _A in

-- Type variables
utest glbcType (tyvar_ "X") with _A in

-- Distributions
let _glbcType = lam c. glbcType (tydist_ (tyfloatc_ c)) in

utest _glbcType _A with _A in
utest _glbcType _M with _A in

-- ┌────────────────────────────┐
-- │ Test dtcEnvGlbc/dtcEnvLubc │
-- └────────────────────────────┘

let genC = lam.
  switch randIntU 0 5
  case 0 then ModA ()
  case 1 then ModPC ()
  case 2 then ModP ()
  case 3 then ModC ()
  case 4 then ModM ()
  end
in

let genEnv = lam.
  dtcEnvOfSeq [
    (_x, tyfloatc_ (genC ())),
    (_y, tyfloatc_ (genC ())),
    (_z, tyfloatc_ (genC ())),
    (_f, tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) (genC ()) _D),
    (_g, tydist_ (tyfloatc_ _A))
  ]
in

repeat
  (lam. let env = genEnv () in
      let minc = dtcEnvGlbc env in
      let maxc = dtcEnvLubc env in
      -- Exit on first failing test
      let onFail = lam. lam.
        error (strJoin "\n" [
          "Failed randomized environment test with:",
          concat "minc: " (dtcCoeffectToString minc),
          concat "maxc: " (dtcCoeffectToString maxc),
          concat "env: " (dtcEnvToString env)
        ])
      in
      utest dtcLeqcEnv minc env with true
        using and else onFail
      in
      let allcs = [ModA (), ModP (), ModC (), ModM ()] in
      -- Test that minc is indeed the maximum coeffect modifier that fulfuills
      -- `dtcLeqcEnv c env`
      iter (lam c.
        if not (dtcLeqc c minc) then
          utest dtcLeqcEnv c env with false
            using (lam a. lam b. not (or a b)) else onFail
          in ()
        else ())
        allcs;
      utest dtcLeqEnvc env maxc with true
        using and else onFail
      in
      -- Test that maxc is indeed the minimum coeffect modifier that fulfuills
      -- `dtcLeqEnvc env c`
      iter (lam c.
        if not (dtcLeqc maxc c) then
          utest dtcLeqEnvc env c with false
            using (lam a. lam b. not (or a b)) else onFail
          in ()
        else ())
        allcs)
  1000;

-- ┌─────────────┐
-- │ Test typeOf │
-- └─────────────┘

let _typeOf = lam env. lam tm. (result.consume (typeOf (dtcEnvOfSeq env) tm)).1 in

let eq =
  -- Either compare the type or the error constructors
  eitherEq
    (lam l. lam r.
      forAll (lam x. x)
        (zipWith (lam l. lam r. eqi (constructorTag l) (constructorTag r)) l r))
    (tupleEq2 dtcEqe eqType)
in

let toString =
  eitherEither
    (lam errs. strJoin "\n" (map typeErrorToString errs))
    (lam t. join [":", dtcEffectToString t.0, " ", type2str t.1])
in
let onFail = utestDefaultToString toString toString in

-- Shorthand types
let arrce = lam ps. lam ret. foldr (lam t. lam to. tyarrowce_ t.0 to t.1 t.2) ret ps in
let arrc = lam ps. arrce (map (lam p. (p.0, p.1, _D)) ps) in
let arre = lam ps. arrce (map (lam p. (p.0, _A, p.1)) ps) in
let arr = lam ps. arrce (map (lam p. (p, _A, _D)) ps) in
let flt = tyfloatc_ in

-- Shorthand terms
let lam_ = nlams_ in
let f = appSeq_ (nvar_ _f) in
let g = appSeq_ (nvar_ _g) in
let h = appSeq_ (nvar_ _h) in
let x = nvar_ _x in
let y = nvar_ _y in
let z = nvar_ _z in
let u = nvar_ _u in
let v = nvar_ _v in
let w = nvar_ _w in

-- Basic tests
utest _typeOf [] (lam_ [(_x, tyint_)] x)
  with Right (_D, arrc [(tyint_, _M)] tyint_)
  using eq else onFail
in

utest _typeOf [(_x, tyint_)] (app_ x x)
  with Left [DTCArrowError (NoInfo (), None ())]
  using eq else onFail
in

utest _typeOf [(_x, tyint_)] (bind_ (nulet_ _y x) y)
  with Right (_D, tyint_)
  using eq else onFail
in

-- Test effect propagation
utest _typeOf [(_f, arrce [(tyint_, _A, _R)] tyint_), (_x, tyint_)] (f [x])
  with Right (_R, tyint_)
  using eq else onFail
in

-- Test subtyping and promotion
utest _typeOf [(_f, arr [flt _A] (flt _A)), (_x, flt _A)] (f [x])
  with Right (_D, flt _A)
  using eq else onFail
in

utest _typeOf [(_f, arr [flt _A] (flt _A)), (_x, flt _P)] (f [x])
  with Right (_D, flt _A)
  using eq else onFail
in

utest _typeOf [(_f, arr [flt _A] tyint_), (_x, tyint_)] (f [x])
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

let env = [
  (_f, arrc [(flt _A, _P), (flt _A, _A)] (flt _A)),
  (_g, arrc [(flt _P, _A), (flt _P, _A)] (flt _P)),
  (_x, flt _P),
  (_y, flt _A)
] in

utest
  _typeOf env  (f [f [x, x], x])
  with Right (_D, flt _P)
  using eq else onFail
in

utest
  _typeOf env  (f [g [f [x, x], x], y])
  with Right (_D, flt _A)
  using eq else onFail
in

utest
  _typeOf env (f [g [f [x, x], y], y])
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _typeOf env (f [g [f [x, y], x], y])
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _typeOf [] (addf_ (float_ 1.) (float_ 1.))
  with Right (_D, flt _M)
  using eq else onFail
in

let env = [
  (_f, arrc [(flt _A, _M)] (flt _A)),
  (_g, arr [flt _M] (flt _M))
] in

utest
  _typeOf env
    (app_
       (lam_ [(_h, arr [flt _A] (flt _M))] (lam_ [(_y, flt _A)] (g [h [y]])))
       (lam_ [(_x, flt _A)] (f [float_ 1.])))
  with Right (_D, arr [flt _A] (flt _M))
  using eq else onFail
in

let env = [
  (_f, arr [flt _M, flt _M] (flt _M)),
  (_x, flt _M),
  (_y, flt _A)
] in

utest
  _typeOf env (addf_ (f [addf_ x (float_ 1.), x]) y)
  with Right (_D, flt _A)
  using eq else onFail
in

let env = [
  (_f, arr [flt _M, flt _M] (flt _M)),
  (_x, flt _P),
  (_y, flt _A)
] in

utest
  _typeOf env (addf_ (f [addf_ x (float_ 1.), x]) y)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

-- Test sequence

utest
  _typeOf [] (seq_ [])
  with Right (_D, tyseq_ (TyBot { info = NoInfo () }))
  using eq else onFail
in

utest
  _typeOf [(_x, flt _A)] (seq_ [x])
  with Right (_D, tyseq_ (flt _A))
  using eq else onFail
in

utest
  _typeOf [(_x, flt _A), (_y, flt _P)] (seq_ [x, y])
  with Right (_D, tyseq_ (flt _A))
  using eq else onFail
in

utest
  _typeOf [
    (_f, arre [(flt _A, _R)] (flt _A)),
    (_g, arre [(flt _A, _D)] (flt _A)),
    (_x, flt _P),
    (_y, flt _M)
  ] (seq_ [f [x], g [y]])
  with Right (_R, tyseq_ (flt _A))
  using eq else onFail
in

-- Test records

utest
  _typeOf [] (utuple_ [])
  with Right (_D, tytuple_ [])
  using eq else onFail
in

utest
  _typeOf [(_x, flt _A), (_y, flt _P)] (utuple_ [x, y])
  with Right (_D, tytuple_ [flt _A, flt _P])
  using eq else onFail
in

utest
  _typeOf [
    (_f, arrce [(flt _A, _P,  _R)] (flt _A)),
    (_g, arrce [(flt _A, _M, _D)] (flt _A)),
    (_x, flt _P),
    (_y, flt _M)
  ] (utuple_ [f [x], g [y]])
  with Right (_R, tytuple_ [flt _P, flt _M])
  using eq else onFail
in

-- Test never

utest _typeOf [] never_ with Right (_D, tybot_) using eq else onFail in

-- Test match

let env = [
  (_x, flt _A)
] in

utest
  _typeOf env (match_ x (npvar_ _y) y x)
  with Right (_D, flt _A)
  using eq else onFail
in

utest
  _typeOf env (match_ x (npvar_ _y) y (float_ 1.))
  with Right (_D, flt _A)
  using eq else onFail
in

let env = [
  (_f, arrce [(flt _P, _M, _D), (flt _P, _P, _D)] (flt _A)),
  (_g, arrce [(flt _A, _P, _R), (flt _M, _A, _D)] (flt _P))
] in

utest
  let f = nvar_ _f in
  let g = nvar_ _g in
  _typeOf env (match_ f pvarw_ f g)
  with Left [DTCHigherOrderTypeError (NoInfo (), None ())]
  using eq else onFail
in

let env = [
  (_x, tyseq_ (flt _A))
] in

utest
  _typeOf env (match_ x (pseqtot_ [npvar_ _y, npvar_ _z]) (seq_ [z, y]) x)
  with Right (_D, tyseq_ (flt _A))
  using eq else onFail
in

utest
  _typeOf env
    (match_ x (pseqedgen_ [npvar_ _y] _z [npvar_ _u])
       (concat_ z (seq_ [y, u])) x)
  with Right (_D, tyseq_ (flt _A))
  using eq else onFail
in

let env = [
  (_x, tytuple_ [flt _A, flt _P, flt _M])
] in

utest
  _typeOf env (tupleproj_ 0 x)
  with Right (_D, flt _A)
  using eq else onFail
in

utest
  _typeOf env (tupleproj_ 1 x)
  with Right (_D, flt _P)
  using eq else onFail
in

utest
  _typeOf env (tupleproj_ 2 x)
  with Right (_D, flt _M)
  using eq else onFail
in

utest
  _typeOf env (tupleproj_ 3 x)
  with Left [DTCPatError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _typeOf [(_x, tyint_)] (match_ x (pint_ 0) x x)
  with Right (_D, tyint_)
  using eq else onFail
in

utest
  _typeOf [(_x, tychar_)] (match_ x (pchar_ '0') x x)
  with Right (_D, tychar_)
  using eq else onFail
in

utest
  _typeOf [(_x, tybool_)] (match_ x ptrue_ x x)
  with Right (_D, tybool_)
  using eq else onFail
in

utest
  _typeOf [(_x, tychar_)] (match_ x (pint_ 0) x x)
  with Left [DTCPatError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _typeOf [(_x, tybool_)] (match_ x (pchar_ '0') x x)
  with Left [DTCPatError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _typeOf [(_x, tyint_)] (match_ x ptrue_ x x)
  with Left [DTCPatError (NoInfo (), None ())]
  using eq else onFail
in

let env = [
  (_x, flt _A),
  (_y, flt _P)
] in

let _tm = lam pat.
  match_ (utuple_ [x, y])
    (pat (ptuple_ [npvar_ _z, pvarw_]) (ptuple_ [pvarw_, npvar_ _z]))
    z never_
in

utest _typeOf env (_tm pand_)
  with Right (_D, flt _A)
  using eq else onFail
in

utest _typeOf env (_tm por_)
  with Right (_D, flt _A)
  using eq else onFail
in

let _tm = match_ x (pnot_ (pint_ 0)) x x in

utest _typeOf [(_x, tyint_)] _tm
  with Right (_D, tyint_)
  using eq else onFail
in

utest _typeOf [(_x, flt _A)] _tm
  with Left [DTCPatError (NoInfo (), None ())]
  using eq else onFail
in

-- Infer

let env = [(_f, arrc [(tyunit_, _M)] (flt _A))] in
let infer__ = infer_ (Default { runs = int_ 1 }) in

utest _typeOf env (infer__ (nvar_ _f))
  with Right (_D, tydist_ (flt _A))
  using eq else onFail
in

utest _typeOf [(_f, arrc [(flt _A, _M)] (flt _A))] (infer__ (nvar_ _f))
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

let infer__ = infer_ (Default { runs = never_ }) in

utest _typeOf env (infer__ (nvar_ _f))
  with Right (_D, tydist_ (flt _A))
  using eq else onFail
in

utest
  _typeOf
    (concat env [(_x, arr [flt _M] tyint_), (_y, flt _A)])
    (infer_ (Default { runs = app_ x y }) (nvar_ _f))
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _typeOf
    (concat env [(_x, arre [(flt _A, _R)] tyint_), (_y, flt _A)])
    (infer_ (Default { runs = app_ x y }) (nvar_ _f))
  with Right (_R, tydist_ (flt _A))
  using eq else onFail
in

-- Assume

utest _typeOf [(_x, tydist_ (flt _A))] (assume_ x)
  with Right (_R, flt _M)
  using eq else onFail
in

utest _typeOf [(_x, flt _A)] (assume_ x)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

-- Observe

utest _typeOf [(_x, tydist_ (flt _A))] (observe_ (float_ 0.) x)
  with Right (_D, tyunit_)
  using eq else onFail
in

utest _typeOf [(_x, tydist_ (flt _A))] (observe_ (int_ 0) x)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

utest _typeOf [(_x, flt _A)] (observe_ (float_ 0.) x)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

-- Weight

utest _typeOf [(_x, flt _A)] (weight_ x)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

utest _typeOf [(_x, flt _P)] (weight_ x)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

utest _typeOf [(_x, flt _M)] (weight_ x)
  with Right (_R, tyunit_)
  using eq else onFail
in

utest _typeOf [] (weight_ (int_ 0))
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

-- Dist

utest _typeOf [(_x, flt _M), (_y, flt _M)] (dist_ (DUniform {a = x, b = y}))
  with Right (_D, tydist_ (flt _M))
  using eq else onFail
in

utest _typeOf [(_x, flt _M)] (dist_ (DBernoulli {p = x}))
  with Right (_D, tydist_ tybool_)
  using eq else onFail
in

utest _typeOf [(_x, flt _M)] (dist_ (DPoisson {lambda = x}))
  with Right (_D, tydist_ tyint_)
  using eq else onFail
in

utest _typeOf [(_x, flt _M), (_y, flt _M)] (dist_ (DBeta {a = x, b = y}))
  with Right (_D, tydist_ (flt _M))
  using eq else onFail
in

utest _typeOf [(_x, flt _M), (_y, flt _M)] (dist_ (DGamma {k = x, theta = y}))
  with Right (_D, tydist_ (flt _M))
  using eq else onFail
in

utest _typeOf [(_x, tyseq_ (flt _M))] (dist_ (DCategorical {p = x}))
  with Right (_D, tydist_ tyint_)
  using eq else onFail
in

utest _typeOf [(_x, tyint_), (_y, tyseq_ (flt _M))]
        (dist_ (DMultinomial {n = x, p = y}))
  with Right (_D, tydist_ (tyseq_ tyint_))
  using eq else onFail
in

utest _typeOf [(_x, flt _M)] (dist_ (DExponential {rate = x}))
  with Right (_D, tydist_ (flt _M))
  using eq else onFail
in

utest _typeOf [(_x, flt _M), (_y, flt _M)] (dist_ (DGaussian {mu = x, sigma = y}))
  with Right (_D, tydist_ (flt _M))
  using eq else onFail
in

utest _typeOf [] (dist_ (DWiener { cps = false, a = unit_ }))
  with Right (_D, tydist_ (arrc [(flt _C, _M)] (flt _A)))
  using eq else onFail
in

utest _typeOf [(_x, flt _M)] (dist_ (DExponential {rate = x}))
  with Right (_D, tydist_ (flt _M))
  using eq else onFail
in

utest _typeOf [(_x, (tyseq_ (tytuple_ [flt _M, flt _M])))]
        (dist_ (DEmpirical {samples = x}))
  with Left [DTCPolyDistError (NoInfo ())]
  using eq else onFail
in

let _test = lam c.
  _typeOf [(_x, flt c)] (dist_ (DExponential {rate = x}))
in

utest _test _A
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

utest _test _P
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

-- Diff

let _test = lam c1. lam c2. lam c3. lam c4. lam c5. lam e. _typeOf [
  (_x, arrce [(flt c1, c2, e)] (flt c3)),
  (_y, flt c4),
  (_z, flt c5)
] (TmDiff {
  fn = x,
  arg = y,
  darg = z,
  ty = tyunknown_,
  info = NoInfo ()
}) in

utest
  _test _A _P _A _A _A _D
  with Right (_D, flt _A)
  using eq else onFail
in

utest
  _test _A _PC _A _A _A _D
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _test _A _C _A _A _A _D
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _test _A _M _A _A _A _D
  with Right (_D, flt _A)
  using eq else onFail
in

utest
  _test _A _P _A _P _P _D
  with Right (_D, flt _P)
  using eq else onFail
in

utest
  _test _A _P _A _C _C _D
  with Right (_D, flt _PC)
  using eq else onFail
in

utest
  _test _A _P _A _M _M _D
  with Right (_D, flt _P)
  using eq else onFail
in

utest
  _test _A _P _P _A _A _D
  with Right (_D, flt _A)
  using eq else onFail
in

utest
  _test _A _P _C _A _A _D
  with Right (_D, flt _A)
  using eq else onFail
in

utest
  _test _A _P _M _A _A _D
  with Right (_D, flt _A)
  using eq else onFail
in

utest
  _test _P _P _A _A _A _D
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _test _M _P _A _A _A _D
  with Left [DTCDiffFnError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _test _A _P _A _A _A _R
  with Left [DTCDiffFnError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _test _P _P _A _A _A _D
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _test _P _P _A _P _A _D
  with Right (_D, flt _A)
  using eq else onFail
in

utest
  _test _P _P _A _C _A _D
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _test _P _P _A _M _A _D
  with Right (_D, flt _A)
  using eq else onFail
in

utest
  _test _M _P _A _P _A _D
  with Left [DTCDiffFnError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _test _M _P _A _M _A _D
  with Left [DTCDiffFnError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _typeOf [
    (_x, arr [tyseq_ (tytuple_ [flt _A, tyint_])] (flt _A)),
    (_y, (tyseq_ (tytuple_ [flt _A, tyint_]))),
    (_z, (tyseq_ (tytuple_ [flt _A, tyint_])))
  ] (diff_ x y z)
  with Left [DTCDiffFnError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _typeOf [
    (_x, arr [flt _A] (tyseq_ (tytuple_ [flt _A, tyint_]))),
    (_y, (flt _A)),
    (_z, (flt _A))
  ] (diff_ x y z)
  with Left [DTCDiffFnError (NoInfo (), None ())]
  using eq else onFail
in

-- Solve

let _test = lam r.
  _typeOf [
    (_x, arrc [(flt r.x, r.arrc1), (flt r.y, r.arrc2)] (flt r.ret)),
    (_y, tytuple_ [flt r.x0, flt r.y0]),
    (_z, flt r.x1)
  ] (solveode_ x y z)
in

utest
  _test {
    x = _A,
    arrc1 = _A,
    y = _A,
    arrc2 = _A,
    ret = _A,
    x0 = _A,
    y0 = _A,
    x1 = _A }
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _test {
    x = _A,
    arrc1 = _A,
    y = _A,
    arrc2 = _A,
    ret = _A,
    x0 = _A,
    y0 = _A,
    x1 = _P }
  with Right (_D, tytuple_ [flt _A, flt _A])
  using eq else onFail
in

utest
  _test {
    x = _C,
    arrc1 = _A,
    y = _A,
    arrc2 = _A,
    ret = _A,
    x0 = _A,
    y0 = _A,
    x1 = _P }
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _test {
    x = _C,
    arrc1 = _A,
    y = _A,
    arrc2 = _A,
    ret = _A,
    x0 = _A,
    y0 = _A,
    x1 = _C }
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _test {
    x = _C,
    arrc1 = _A,
    y = _A,
    arrc2 = _A,
    ret = _A,
    x0 = _C,
    y0 = _A,
    x1 = _C }
  with Right (_D, tytuple_ [flt _A, flt _A])
  using eq else onFail
in

utest
  _test {
    x = _M,
    arrc1 = _A,
    y = _A,
    arrc2 = _A,
    ret = _A,
    x0 = _M,
    y0 = _A,
    x1 = _M }
  with Left [DTCSolveODEModelError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _test {
    x = _A,
    arrc1 = _A,
    y = _P,
    arrc2 = _A,
    ret = _A,
    x0 = _A,
    y0 = _P,
    x1 = _P }
  with Left [DTCSolveODEModelError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _test {
    x = _C,
    arrc1 = _C,
    y = _A,
    arrc2 = _A,
    ret = _A,
    x0 = _C,
    y0 = _C,
    x1 = _C }
  with Right (_D, tytuple_ [flt _C, flt _C])
  using eq else onFail
in

-- Sequence operations

utest
  _typeOf [
    (_x, tyseq_ (flt _A))
  ] (app_ (uconst_ (CSet ())) x)
  with Right (_D, arr [tyint_, flt _A] (tyseq_ (flt _A)))
  using eq else onFail
in

utest
  _typeOf [
    (_x, tyseq_ (flt _A))
  ] (app_ (uconst_ (CGet ())) x)
  with Right (_D, arr [tyint_] (flt _A))
  using eq else onFail
in

utest
  _typeOf [
    (_x, flt _A)
  ] (app_ (uconst_ (CCons ())) x)
  with Right (_D, arr [tyseq_ (flt _A)] (tyseq_ (flt _A)))
  using eq else onFail
in

utest
  _typeOf [
    (_x, tyseq_ (flt _A))
  ] (app_ (uconst_ (CSnoc ())) x)
  with Right (_D, arr [(flt _A)] (tyseq_ (flt _A)))
  using eq else onFail
in

utest
  _typeOf [
    (_x, tyseq_ (flt _A))
  ] (app_ (uconst_ (CConcat ())) x)
  with Right (_D, arr [tyseq_ (flt _A)] (tyseq_ (flt _A)))
  using eq else onFail
in

utest
  _typeOf [
    (_x, tyseq_ (flt _A))
  ] (app_ (uconst_ (CLength ())) x)
  with Right (_D, tyint_)
  using eq else onFail
in

utest
  _typeOf [
    (_x, tyseq_ (flt _A))
  ] (app_ (uconst_ (CReverse ())) x)
  with Right (_D, tyseq_ (flt _A))
  using eq else onFail
in

utest
  _typeOf [
    (_x, tyseq_ (flt _A))
  ] (app_ (uconst_ (CHead ())) x)
  with Right (_D, flt _A)
  using eq else onFail
in

utest
  _typeOf [
    (_x, tyseq_ (flt _A))
  ] (app_ (uconst_ (CTail ())) x)
  with Right (_D, tyseq_ (flt _A))
  using eq else onFail
in

let _test = lam c.
  _typeOf [
    (_x, tyseq_ (flt _A))
  ] (app_ (uconst_ c) x)
in

iter
  (lam c. utest _test c with Right (_D, tybool_) using eq else onFail in ())
  [CNull (), CIsList (), CIsRope ()];

let _test = lam e.
  _typeOf [
    (_x, arre [(flt _A, e)] (flt _P))
  ] (app_ (uconst_ (CMap ())) x)
in

let _expected = lam e.
  Right (_D, arre [(tyseq_ (flt _A), e)] (tyseq_ (flt _P)))
in

utest _test _D with _expected _D using eq else onFail in
utest _test _R with _expected _R using eq else onFail in

let _test = lam e1. lam e2.
  _typeOf [
    (_x, arre [(tyint_, e1), (flt _A, e2)] (flt _P))
  ] (app_ (uconst_ (CMapi ())) x)
in

let _expected = lam e.
  Right (_D, arre [(tyseq_ (flt _A), e)] (tyseq_ (flt _P)))
in

utest _test _D _D with _expected _D using eq else onFail in
utest _test _R _D with _expected _R using eq else onFail in
utest _test _D _R with _expected _R using eq else onFail in
utest _test _R _R with _expected _R using eq else onFail in

let _test = lam e.
  _typeOf [
    (_x, arre [(flt _A, e)] tyunit_)
  ] (app_ (uconst_ (CIter ())) x)
in

let _expected = lam e.
  Right (_D, arre [(tyseq_ (flt _A), e)] tyunit_)
in

utest _test _D with _expected _D using eq else onFail in
utest _test _R with _expected _R using eq else onFail in

let _test = lam e1. lam e2.
  _typeOf [
    (_x, arre [(tyint_, e1), (flt _A, e2)] tyunit_)
  ] (app_ (uconst_ (CIteri ())) x)
in

let _expected = lam e.
  Right (_D, arre [(tyseq_ (flt _A), e)] tyunit_)
in

utest _test _D _D with _expected _D using eq else onFail in
utest _test _R _D with _expected _R using eq else onFail in
utest _test _D _R with _expected _R using eq else onFail in
utest _test _R _R with _expected _R using eq else onFail in

let _test = lam e1. lam e2.
  _typeOf [
    (_x, arre [(tyint_, e1), (flt _A, e2)] tyint_)
  ] (app_ (uconst_ (CFoldl ())) x)
in

let _expected = lam e.
  Right (_D, arre [(tyint_, _D), (tyseq_ (flt _A), e)] (tyint_))
in

utest _test _D _D with _expected _D using eq else onFail in
utest _test _R _D with _expected _R using eq else onFail in
utest _test _D _R with _expected _R using eq else onFail in
utest _test _R _R with _expected _R using eq else onFail in

let _test = lam e1. lam e2.
  _typeOf [
    (_x, arre [(flt _A, e2), (tyint_, e1)] tyint_)
  ] (app_ (uconst_ (CFoldr ())) x)
in

let _expected = lam e.
  Right (_D, arre [(tyint_, _D), (tyseq_ (flt _A), e)] (tyint_))
in

utest _test _D _D with _expected _D using eq else onFail in
utest _test _R _D with _expected _R using eq else onFail in
utest _test _D _R with _expected _R using eq else onFail in
utest _test _R _R with _expected _R using eq else onFail in

iter
  (lam c.
    let _test = lam e.
      _typeOf [
        (_x, tyint_),
        (_y, arre [(tyint_, e)] (flt _A))
     ] (appf2_ (uconst_ c) x y)
    in
    let _expected = lam e. Right (e, tyseq_ (flt _A)) in
    utest _test _D with _expected _D using eq else onFail in
    utest _test _R with _expected _R using eq else onFail in
    ())
  [CCreate (), CCreateList (), CCreateRope ()];

utest
  _typeOf [
    (_x, tyseq_ (flt _A))
  ] (app_ (uconst_ (CSplitAt ())) x)
  with Right (_D, arr [tyint_] (tytuple_ [tyseq_ (flt _A), tyseq_ (flt _A)]))
  using eq else onFail
in

utest
  _typeOf [
    (_x, tyseq_ (flt _A))
  ] (app_ (uconst_ (CSubsequence ())) x)
  with Right (_D, arr [tyint_, tyint_] (tyseq_ (flt _A)))
  using eq else onFail
in

-- Dist Operations

utest
  _typeOf [
    (_x, tydist_ tyint_)
  ] (app_ (uconst_ (CDistEmpiricalSamples ())) x)
  with Right (_D, tytuple_ [tyseq_ tyint_, tyseq_ (flt _M)])
  using eq else onFail
in

utest
  _typeOf [
    (_x, tydist_ tyint_)
  ] (app_ (uconst_ (CDistEmpiricalDegenerate ())) x)
  with Right (_D, tybool_)
  using eq else onFail
in

utest
  _typeOf [
    (_x, tydist_ tyint_)
  ] (app_ (uconst_ (CDistEmpiricalNormConst ())) x)
  with Right (_D, flt _M)
  using eq else onFail
in

utest
  _typeOf [
    (_x, tydist_ tyint_)
  ] (app_ (uconst_ (CDistEmpiricalAcceptRate ())) x)
  with Right (_D, flt _M)
  using eq else onFail
in

utest
  _typeOf [
    (_x, tydist_ (flt _M))
  ] (app_ (uconst_ (CDistExpectation ())) x)
  with Right (_D, flt _M)
  using eq else onFail
in

-- Utest

utest _typeOf [(_x, flt _A), (_y, flt _A), (_z, flt _A)] (bind_ (utest_ x y) z)
  with Right (_D, flt _A)
  using eq else onFail
in

utest _typeOf [
  (_x, flt _A),
  (_y, flt _A),
  (_z, flt _A),
  (_u, arr [flt _A, flt _A] tybool_)
] (bind_ (utestu_ x y u) z)
  with Right (_D, flt _A)
  using eq else onFail
in

utest _typeOf [
  (_x, flt _A),
  (_y, flt _A),
  (_z, flt _A),
  (_u, arr [flt _A, flt _A] tybool_),
  (_v, arr [flt _A, flt _A] tybool_)
] (bind_ (utestuo_ x y u v) z)
  with Right (_D, flt _A)
  using eq else onFail
in

-- ┌───────────────────────┐
-- │ Modified Old Examples │
-- └───────────────────────┘

-- Example 1

let env = [
  (_f, arrc [(flt _M, _M)] (flt _M))
] in

let _tm = lam c.
  nlam_ _u (tytuple_ [flt _M, flt c])
    (matchex_ u (ptuple_ [npvar_ _x, npvar_ _y]) (addf_ (f [x]) y))
in

let _ty = lam c1. lam c2. lam c3.
  arrc [(tytuple_ [flt _M, flt c1], c3)] (flt c2)
in

utest _typeOf env (_tm _A)
  with Right (_D, _ty _A _A _M)
  using eq else onFail
in

utest _typeOf env (_tm _P)
  with Right (_D, (_ty _P _P _M))
  using eq else onFail
in

utest _typeOf env (_tm _M)
  with Right (_D, (_ty _M _M _M))
  using eq else onFail
in

let _tm = lam c. lam fst. lam snd.
  nlam_ _z (flt c) (app_ (_tm c) (utuple_ [fst, snd]))
in

let _ty = lam c1. lam c2. lam c3.
  arrc [(flt c1, c2)] (flt c3)
in

utest _typeOf env (_tm _A (float_ 0.) z)
  with Right (_D, _ty _A _M _A)
  using eq else onFail
in

utest _typeOf env (_tm _M z (float_ 0.))
  with Right (_D, _ty _M _M _M)
  using eq else onFail
in

utest _typeOf env (_tm _A z (float_ 0.))
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

-- Example 2

let _tm = lam c. nlam_ _x (flt c) (if_ (gtf_ x (float_ 0.)) x (negf_ x)) in

utest _typeOf [] (_tm _A)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

utest _typeOf [] (_tm _P)
  with Right (_D, arrc [(flt _P, _M)] (flt _P))
  using eq else onFail
in

utest _typeOf [] (_tm _M)
  with Right (_D, arrc [(flt _M, _M)] (flt _M))
  using eq else onFail
in

-- Example 3

let expectation_ = app_ (uconst_ (CDistExpectation ())) in

utest
  _typeOf [] (nlam_ _x (flt _P) (expectation_ (infer__ (nlam_ _y tyunit_ x))))
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail
in

utest
  _typeOf []
    (nlam_ _x (flt _P)
       (mulf_ x (expectation_ (infer__ (nlam_ _y tyunit_ (float_ 1.))))))
  with Right (_D, arrc [(flt _P, _M)] (flt _P))
  using eq else onFail
in

()
