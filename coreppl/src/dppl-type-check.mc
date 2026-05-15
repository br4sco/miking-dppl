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
include "eqset.mc"

include "./dist.mc"
include "./coreppl.mc"

-- ┌───────────────────────────────┐
-- │ Effect and Coeffect Modifiers │
-- └───────────────────────────────┘

-- Effects are either deterministic (D) or random (R).
type DTCEffect
con ModD : () -> DTCEffect
con ModR : () -> DTCEffect

let dtcEff = [ModD (), ModR ()]

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

-- The meet of two effects.
let dtcMeete : DTCEffect -> DTCEffect -> DTCEffect
  = lam a. lam b.
    switch (a, b)
    case (ModD _, _) then a
    case (_ , ModD _) then b
    case _ then a
    end

utest dtcMeete (ModD ()) (ModD ()) with ModD ()
utest dtcMeete (ModD ()) (ModR ()) with ModD ()
utest dtcMeete (ModR ()) (ModD ()) with ModD ()
utest dtcMeete (ModR ()) (ModR ()) with ModR ()

-- The join of two effects.
let dtcJoine : DTCEffect -> DTCEffect -> DTCEffect
  = lam a. lam b.
    switch (a, b)
    case (ModR _, _) then a
    case (_ , ModR _) then b
    case _ then a
    end

utest dtcJoine (ModD ()) (ModD ()) with ModD ()
utest dtcJoine (ModD ()) (ModR ()) with ModR ()
utest dtcJoine (ModR ()) (ModD ()) with ModR ()
utest dtcJoine (ModR ()) (ModR ()) with ModR ()

-- Multiplication over effects (e ⋅ e).
let dtcMule : DTCEffect -> DTCEffect -> DTCEffect
  = dtcJoine

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

-- Base regularites are either analytic (A), piecewise analytic under analytic
-- partitioning (P), continuous (C).
type DTCReg
con ModA : () -> DTCReg
con ModP : () -> DTCReg
con ModC : () -> DTCReg

let dtcReg = [ModC (), ModP (), ModA ()]

let dtcRegToString : DTCReg -> String = lam c.
  switch c
  case ModA _  then "ModA"
  case ModP _  then "ModP"
  case ModC _  then "ModC"
  end

let _dtcRegToInt : DTCReg -> Int = lam c.
  switch c
  case ModC  _ | ModP _ then 0   -- NOTE(oerikss, 2025-10-13): We cannot order C and P.
  case ModA  _          then 1
  end

-- Less than or equal over coeffects (c ≤ c), where P < A and C < A.
let dtcLeqc : DTCReg -> DTCReg -> Bool
  = lam a. lam b.
    match (a, b) with (ModC _, ModP _) | (ModP _, ModC _) then false
    else leqi (_dtcRegToInt a) (_dtcRegToInt b)

utest dtcLeqc (ModA ()) (ModA ()) with true
utest dtcLeqc (ModA ()) (ModP ()) with false
utest dtcLeqc (ModA ()) (ModC ()) with false

utest dtcLeqc (ModP ()) (ModA ()) with true
utest dtcLeqc (ModP ()) (ModP ()) with true
utest dtcLeqc (ModP ()) (ModC ()) with false

utest dtcLeqc (ModC ()) (ModA ()) with true
utest dtcLeqc (ModC ()) (ModP ()) with false
utest dtcLeqc (ModC ()) (ModC ()) with true

-- Equality over coeffects (c = c).
let dtcEqc : DTCReg -> DTCReg -> Bool
  = lam a. lam b.
    switch (a, b)
    case (ModC _, ModC _)
       | (ModP _, ModP _)
       | (ModA _, ModA _) then true
    case _ then false
    end

utest dtcEqc (ModA ()) (ModA ()) with true
utest dtcEqc (ModA ()) (ModP ()) with false
utest dtcEqc (ModA ()) (ModC ()) with false

utest dtcEqc (ModP ()) (ModA ()) with false
utest dtcEqc (ModP ()) (ModP ()) with true
utest dtcEqc (ModP ()) (ModC ()) with false

utest dtcEqc (ModC ()) (ModA ()) with false
utest dtcEqc (ModC ()) (ModP ()) with false
utest dtcEqc (ModC ()) (ModC ()) with true

-- Compare function for regularities. This function enforces a total order on
-- regularities.
let dtcCmpc : DTCReg -> DTCReg -> Int = lam c. lam d.
  switch (c,d)
  case (ModC _, ModP _) then -1
  case (ModP _, ModC _) then 1
  case _ then subi (_dtcRegToInt c) (_dtcRegToInt d)
  end

utest sort dtcCmpc [ModA (), ModP (), ModC ()]
  with [ModC (), ModP (), ModA ()]
utest sort (flip dtcCmpc) [ModC (), ModP (), ModA ()]
  with [ModA (), ModP (), ModC ()]

-- Coeffect sets
type DTCRegSet = [DTCReg]

let dtcXInsert : DTCReg -> DTCRegSet -> DTCRegSet = eqsetInsert dtcEqc
let dtcXMem : DTCReg -> DTCRegSet -> Bool = eqsetMem dtcEqc
let dtcXUnion : DTCRegSet -> DTCRegSet -> DTCRegSet = eqsetUnion dtcEqc
let dtcXIntersection : DTCRegSet -> DTCRegSet -> DTCRegSet = eqsetIntersection dtcEqc
let dtcXIsSubsetEq : DTCRegSet -> DTCRegSet -> Bool = eqsetIsSubsetEq dtcEqc
let dtcXEq : DTCRegSet -> DTCRegSet -> Bool = eqsetEqual dtcEqc

let dtcRegSetToString : DTCRegSet -> String = lam cs.
  join ["{", strJoin ", " (map dtcRegToString cs), "}"]

let dtcXDown : DTCReg -> DTCRegSet = lam c.
  switch c
  case ModA _ then [ModC (), ModP (), ModA ()]
  case ModP _ then [ModP ()]
  case ModC _ then [ModC ()]
  end

let dtcPC : DTCRegSet = dtcXUnion (dtcXDown (ModP ())) (dtcXDown (ModC ()))

let dtcXbar : DTCRegSet -> DTCRegSet =
  lam cs. filter (lam c. any (dtcLeqc c) cs) dtcReg

-- Returns max regularities.
let dtcXMax : DTCRegSet -> DTCRegSet = lam cs.
  let cs = sort (flip dtcCmpc) (distinct dtcEqc cs) in
  switch cs
  case [] then []
  case [ModP _, ModC _] ++ _ then [ModP (), ModC ()]
  case [c] ++ _ then [c]
  end

utest dtcXMax (dtcXDown (ModA ())) with [ModA ()]
utest dtcXMax (dtcXDown (ModP ())) with [ModP ()]
utest dtcXMax (dtcXDown (ModC ())) with [ModC ()]
utest dtcXMax [] with []
utest dtcXMax dtcPC with [ModP (), ModC ()]

-- Returns min regularities.
let dtcXMin : DTCRegSet -> DTCRegSet = lam cs.
  let cs = sort dtcCmpc (distinct dtcEqc cs) in
  switch cs
  case [] then []
  case [ModC _, ModP _] ++ _ then [ModC (), ModP ()]
  case [c] ++ _ then [c]
  end

utest dtcXMin [] with []
utest dtcXMin (dtcXDown (ModA ())) with [ModC (), ModP ()]
utest dtcXMin (dtcXDown (ModP ())) with [ModP ()]
utest dtcXMin (dtcXDown (ModC ())) with [ModC ()]
utest dtcXMin dtcPC with [ModC (), ModP ()]
utest dtcXMin [ModA (), ModC ()] with [ModC ()]

-- Returns the surface below the regularity `c` according to the partial order
-- of regularities.
let dtcLowerSurface : DTCReg -> DTCRegSet = lam c.
  switch c
  case ModA _ then [ModC (), ModP ()]
  case ModC _ | ModP _ then []
  end

-- ┌───────────────┐
-- │ Annotated AST │
-- └───────────────┘

lang DTCAstBase = Ast + Eq
  -- NOTE(oerikss, 2024-10-07): The semantic functions in this fragment assumes
  -- that types and terms have been symbolized. I.e., it relies on unique
  -- identifiers in types and terms.

  -- ┌───────────┐
  -- │ Utilities │
  -- └───────────┘

  -- Drops decorations from types
  sem eraseDecorationsType : Type -> Type
  sem eraseDecorationsType =| ty -> smap_Type_Type eraseDecorationsType ty

  -- Drops decorations from terms
  sem eraseDecorations : Expr -> Expr
  sem eraseDecorations =| tm ->
    smap_Expr_Expr eraseDecorations (smap_Expr_Type eraseDecorationsType tm)

  -- Is this type first order. Defaults to true so higher order types should
  -- extend this.
  sem isFirstOrder : Type -> Bool
  sem isFirstOrder =| ty ->
    sfold_Type_Type (lam acc. lam ty. and acc (isFirstOrder ty)) true ty

  -- Converts between MExpr types and DDPL types. In particular it replaces
  -- MExpr float and arrow types to the corresponding DPPL types.
  sem fromMExprTy : Type -> Type
  sem fromMExprTy =| ty -> smap_Type_Type fromMExprTy ty

  -- ┌───────────────────────┐
  -- │ Regularity Operations │
  -- └───────────────────────┘

  -- X ⋅ T
  sem mulXType : DTCRegSet -> Type -> Type
  sem mulXType cs =| ty -> smap_Type_Type (mulXType cs) ty

  -- Accumulates the least conservative X from T s.t. T ≤ X.
  sem accPromote : DTCRegSet -> Type -> DTCRegSet
  sem accPromote acc =| ty -> sfold_Type_Type accPromote acc ty

  -- The least conservative augmentation of X s.t. X ~ T.
  sem accApp : DTCRegSet -> Type -> DTCRegSet
  sem accApp acc =| ty -> sfold_Type_Type accApp acc ty

  -- Sets all regularities in T to X.
  sem withX : DTCRegSet -> Type -> Type
  sem withX cs =| ty -> smap_Type_Type (withX cs) ty

  -- ┌───────────┐
  -- │ Subtyping │
  -- └───────────┘

  -- NOTE(oerikss, 2024-10-04): The default case only compares contructors of
  -- the types. The extension of `DTCAstBase` are reponsible to handle all
  -- cases where `subtype` needs to be applied recursively.

  -- `subtype (lhs, rhs)` is true if `lhs` is a subtype of `rhs`
  sem subtype : Type -> Type -> Bool
  sem subtype ty1 =| ty2 -> subtypeH (ty1, ty2)

  sem subtypeH : (Type, Type) -> Bool
  sem subtypeH =| (lhs, rhs) -> eqi (constructorTag lhs) (constructorTag rhs)

  -- `joinType (lhs, rhs)` returns the join of `lhs` and `rhs` if there is such
  -- as concrete type. Otherwise it returns `None ()` which can be considered
  -- the top type.
  sem joinType : Type -> Type -> Option Type
  sem joinType ty1 =| ty2 -> joinTypeH (ty1, ty2)

  sem joinTypeH : (Type, Type) -> Option Type
  sem joinTypeH =| (lhs, rhs) ->
    if eqi (constructorTag lhs) (constructorTag rhs) then Some lhs else None ()

  -- `meetType (lhs, rhs)` returns the meet of `lhs` and `rhs`.
  sem meetType : Type -> Type -> Type
  sem meetType ty1 =| ty2 -> meetTypeH (ty1, ty2)

  sem meetTypeH : (Type, Type) -> Type
end

lang DTCBottomTypeAst = DTCAstBase + UnknownTypeAst + PrettyPrint
  syn Type =| TyBot {info : Info}

  -- ┌───────────┐
  -- │ Type sems │
  -- └───────────┘

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

  -- ┌───────────┐
  -- │ Utilities │
  -- └───────────┘

  sem eraseDecorationsType =
  | TyBot r -> TyUnknown { info = r.info }

  -- ┌───────────────────────┐
  -- │ Regularity Operations │
  -- └───────────────────────┘

  -- ┌───────────┐
  -- │ Subtyping │
  -- └───────────┘

  sem subtypeH =
  | (TyBot _, _) -> true
  | (! TyBot _, TyBot _) -> false

  sem joinTypeH =
  | (TyBot _, ty) | (ty, TyBot _) -> Some ty

  sem meetTypeH =
  | (TyBot r, ty) | (ty, TyBot r) -> TyBot r
  | (lhs, rhs) ->
    if eqi (constructorTag lhs) (constructorTag rhs) then lhs
    else TyBot { info = infoTy lhs }
end

let tybot_ = use DTCBottomTypeAst in TyBot { info = NoInfo () }

lang DTCFloatTypeAst = DTCAstBase + FloatTypeAst + PrettyPrint
  -- Float types are annotated with coffects
  syn Type =| TyFloatC {info : Info, cs : DTCRegSet}

  -- ┌───────────┐
  -- │ Type sems │
  -- └───────────┘

  -- Setters/Getters
  sem tyWithInfo info =| TyFloatC r -> TyFloatC { r with info = info }
  sem infoTy =| TyFloatC r -> r.info

  -- Eq
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyFloatC r ->
    match unwrapType lhs with TyFloatC l then
      if dtcXEq l.cs r.cs then Some free else None ()
    else None ()
  -- PPrint
  sem typePrecedence = | TyFloatC _ -> 1
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyFloatC r ->
    if dtcXEq r.cs (dtcXDown (ModC ())) then (env, "FloatC")
    else if dtcXEq r.cs (dtcXDown (ModP ())) then (env, "FloatP")
         else if dtcXEq r.cs (dtcXDown (ModA ())) then (env, "FloatA")
              else if dtcXEq r.cs dtcPC then (env, "FloatPC")
                   else (env, concat "Float" (dtcRegSetToString r.cs))

  -- ┌───────────┐
  -- │ Utilities │
  -- └───────────┘

  -- Builder
  sem tyfloatc_ : DTCReg -> Type
  sem tyfloatc_ =| c -> TyFloatC { info = NoInfo (), cs = dtcXDown c }

  sem tyfloatX_ : DTCRegSet -> Type
  sem tyfloatX_ =| cs -> TyFloatC { info = NoInfo (), cs = cs }

  sem ityfloatc_ : Info -> DTCReg -> Type
  sem ityfloatc_ info =| c -> TyFloatC { info = info, cs = dtcXDown c }

  sem ityfloatX_ : Info -> DTCRegSet -> Type
  sem ityfloatX_ info =| cs -> TyFloatC { info = info, cs = cs }

  -- Conversions
  sem eraseDecorationsType =
  | TyFloatC r -> TyFloat { info = r.info }

  sem fromMExprTy =
  | TyFloat r -> TyFloatC { info = r.info, cs = [] }

  -- ┌───────────────────────┐
  -- │ Regularity Operations │
  -- └───────────────────────┘

  sem mulXType cs =
  | TyFloatC r -> TyFloatC { r with cs = dtcXbar (dtcXIntersection cs r.cs) }

  sem accPromote acc =
  | TyFloatC r -> dtcXUnion acc (dtcXMax r.cs)

  sem withX cs =
  | TyFloatC r -> TyFloatC { r with cs = cs }

  -- ┌───────────┐
  -- │ Subtyping │
  -- └───────────┘

  sem subtypeH =
  | (TyFloatC l, TyFloatC r) -> dtcXIsSubsetEq l.cs r.cs

  sem joinTypeH =
  | (TyFloatC l, TyFloatC r) ->
    Some (TyFloatC { l with cs = dtcXUnion l.cs r.cs })

  sem meetTypeH =
  | (TyFloatC l, TyFloatC r) ->
    TyFloatC { l with cs = dtcXIntersection l.cs r.cs }
end

lang DTCFunTypeAst = DTCBottomTypeAst + FunTypeAst + PrettyPrint
  -- Arrow types are annotated with effects and regularities
  syn Type =| TyArrowCE {
    info : Info, from : Type, to : Type, cs: DTCRegSet, e : DTCEffect }

  -- ┌───────────┐
  -- │ Type sems │
  -- └───────────┘

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
        if dtcXEq l.cs r.cs then
          if dtcEqe l.e r.e then eqTypeH typeEnv free l.to r.to
          else None ()
        else None ()
      else None ()
    else None ()

  -- Pprint
  sem typePrecedence =
  | TyArrowCE r -> 0

  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyArrowCE r ->
    match printTypeParen indent 1 env r.from with (env, from) in
    match r.e with ModR _ then
      match printTypeParen indent 2 env r.to with (env, to) in
      (env, join
              [ from, " ->"
              , dtcRegSetToString r.cs
              , "(", dtcEffectToString r.e, " ", to, ")"
              ])
    else
      match getTypeStringCode indent env r.to with (env, to) in
      (env, join [from, " ->", dtcRegSetToString r.cs, " ", to])

  -- ┌───────────┐
  -- │ Utilities │
  -- └───────────┘

  -- Builder
  sem tyarrowXe_ : Type -> Type -> DTCRegSet -> DTCEffect -> Type
  sem tyarrowXe_ from to cs =| e ->
    TyArrowCE { info = NoInfo (), from = from, to = to, cs = cs, e = e }

  sem ityarrowXe_ : Info -> Type -> Type -> DTCRegSet -> DTCEffect -> Type
  sem ityarrowXe_ info from to cs =| e ->
    TyArrowCE { info = info, from = from, to = to, cs = cs, e = e }

  -- Conversions
  sem eraseDecorationsType =
  | TyArrowCE r ->
    smap_Type_Type eraseDecorationsType
      (TyArrow { info = r.info, from = r.from, to = r.to })

  sem fromMExprTy =
  | TyArrow r ->
    smap_Type_Type fromMExprTy
      (ityarrowXe_ r.info r.from r.to [] (ModD ()))

  -- ┌───────────────────────┐
  -- │ Regularity Operations │
  -- └───────────────────────┘

  sem mulXType cs =
  | TyArrowCE r -> TyArrowCE { r with cs = dtcXIntersection cs r.cs }

  sem tildeXType cs =
  | TyArrowCE r ->
    let xs = distinct dtcEqc cs in
    let ys = distinct dtcEqc r.cs in
    let xsCupYs = dtcXIntersection xs ys in
    forAll (lam x.
      forAll (lam y.
        if dtcLeqc x y then
          any (lam z. and (dtcLeqc x z) (dtcLeqc z y)) xsCupYs
        else true)
        ys) xs

  sem accPromote acc =
  | TyArrowCE r -> dtcXUnion acc r.cs

  sem accApp acc =
  | TyArrowCE r ->
    foldl (lam acc. lam x. dtcXUnion acc (dtcXMin (filter (dtcLeqc x) r.cs))) acc acc

  sem withX cs =
  | TyArrowCE r -> TyArrowCE { r with cs = cs }

  -- ┌───────────┐
  -- │ Subtyping │
  -- └───────────┘

  sem subtypeH =
  | (TyArrowCE l, TyArrowCE r) ->
    if and (dtcXIsSubsetEq l.cs r.cs) (dtcLeqe l.e r.e)
    then and (subtype r.from l.from) (subtype l.to r.to)
    else false

  sem joinTypeH =
  | (TyArrowCE l, TyArrowCE r) ->
    optionBind (joinType l.to r.to) (lam to.
      Some (TyArrowCE {
        l with
        from = meetType l.from r.from,
        to = to,
        cs = dtcXUnion l.cs r.cs,
        e = dtcJoine l.e r.e }))

  sem meetTypeH =
  | (TyArrowCE l, TyArrowCE r) ->
    optionMapOr (TyBot { info = l.info }) (lam from.
      TyArrowCE {
        l with
        from = from,
        to = meetType l.to r.to,
        cs = dtcXIntersection l.cs r.cs,
        e = dtcMeete l.e r.e })
      (joinType l.from r.from)
end

lang DTCSeqTypeAst = DTCAstBase + SeqTypeAst
  -- ┌───────────────────────┐
  -- │ Regularity Operations │
  -- └───────────────────────┘

  -- ┌───────────┐
  -- │ Subtyping │
  -- └───────────┘

  sem subtypeH =
  | (TySeq l, TySeq r) -> subtype l.ty r.ty

  sem joinTypeH =
  | (TySeq l, TySeq r) ->
    optionBind (joinType l.ty r.ty) (lam ty. Some (TySeq { l with ty = ty }))

  sem meetTypeH =
  | (TySeq l, TySeq r) -> TySeq { l with ty = meetType l.ty r.ty }
end

lang DTCRecordTypeAst = DTCBottomTypeAst + RecordTypeAst
  -- ┌───────────────────────┐
  -- │ Regularity Operations │
  -- └───────────────────────┘

  -- ┌───────────┐
  -- │ Subtyping │
  -- └───────────┘

  sem subtypeH =
  | (TyRecord l, TyRecord r) ->
    let m = mapMerge
              (lam l. lam r.
                switch (l, r)
                case (None _, _) | (_, None _) then Some false
                case (Some l, Some r) then Some (subtype l r)
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
            case (Some l, Some r) then f l r
            end)
          l.fields r.fields
      in
      if eqi nl (mapSize fields) then
        Some (TyRecord { l with fields = fields })
      else None ()
    else None ()

  sem joinTypeH =
  | (TyRecord l, TyRecord r) ->
    let nl = mapSize l.fields in
    if eqi nl (mapSize r.fields) then
      let fields =
        mapMerge
          (lam l. lam r.
            switch (l, r)
            case (None _, _) | (_, None _) then None ()
            case (Some l, Some r) then joinType l r
            end)
          l.fields r.fields
      in
      if eqi nl (mapSize fields) then
        Some (TyRecord { l with fields = fields })
      else None ()
    else None ()

  sem meetTypeH =
  | (TyRecord l, TyRecord r) ->
    let bot = TyBot { info = l.info } in
    if mapEq (lam. lam. true) l.fields r.fields then
      let fields =
        mapMerge
          (lam l. lam r.
            switch (l, r)
            case (None _, _) | (_, None _) then error "Impossible"
            case (Some l, Some r) then Some (meetType l r)
            end)
          l.fields r.fields
      in
      TyRecord { l with fields = fields }
    else bot
end

lang DTCVarTypeAst = DTCAstBase + VarTypeAst + DTCBottomTypeAst
  sem subtypeH =
  | (TyVar l, TyVar r) -> nameEq l.ident r.ident

  sem joinTypeH =
  | (TyVar l, TyVar r) ->
    if nameEq l.ident r.ident then Some (TyVar l)
    else None ()

  sem meetTypeH =
  | arg & (TyVar l, TyVar _) ->
    optionGetOr (TyBot { info = l.info }) (uncurry joinType arg)
end

lang DTCDistTypeAst =  DTCAstBase + Dist
  sem subtypeH =
  | (TyDist l, TyDist r) -> subtype l.ty r.ty

  sem _dtcDistJoinMeet f l =| r ->
    optionBind (f (l.ty, r.ty)) (lam ty. Some (TyDist { l with ty = ty }))

  sem joinTypeH =
  | (TyDist l, TyDist r) ->
    optionBind (joinType l.ty r.ty) (lam ty. Some (TyDist { l with ty = ty }))

  sem meetTypeH =
  | (TyDist l, TyDist r) ->
    TyDist { l with ty = meetType l.ty r.ty }
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

  -- The domain of the type environment.
  sem dtcEnvDomain : DTCReg -> Set Name
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

  -- String representation of the typing environment
  sem dtcEnvToString : DTCEnv -> String
  sem dtcEnvToString =| env ->
    strJoin ", "
      (map (lam t. join [nameGetStr t.0, ":", type2str t.1]) (dtcEnvToSeq env))

  -- Weaken the type environment by removing a set of identifiers from its
  -- domain.
  sem dtcEnvWeaken : Set Name -> DTCEnv -> DTCEnv
  sem dtcEnvWeaken idents =| env ->
    mapFilterWithKey (lam ident. lam. setMem ident idents) env

  sem dtcEnvAccPromote : DTCEnv -> DTCRegSet
  sem dtcEnvAccPromote =| env ->
    mapFoldWithKey (lam acc. lam. accPromote acc) [] env
end

-- ┌──────────────┐
-- │ Type Checker │
-- └──────────────┘

lang DTCTypeError = Ast + ConstAst + DTCEnv + DTCFloatTypeAst + PrettyPrint
  syn DTCTypeError =
  -- NOTE(oerikss, 2024-10-08): The error parameters are optional to make
  -- testing errors easier.
  | DTCTypeError Info
  | DTCArrowError (Info, Option Type)
  | DTCArgError (Info, Option (Type, Type))
  | DTCJoinError (Info, Option (Type, Type))
  | DTCPatError (Info, Option Type)
  | DTCAnotError Info
  --   | DTCSolveODEModelError (Info, Option Type)
  | DTCDiffFnError (Info, Option (DTCReg, Type))
  | DTCDiffFnNotRnError (Info, Option Type)
  | DTCPolyDistError Info
  | DTCPolyConstError Info
  | DTCUnuspportedTermError (Info, Option Expr)
  | DTCInvalidContextError (Info, Option (Name))
  --   | DTCContextConstraintError (Info, Option (DTCReg,  DTCEnv))
  --   | DTCHigherOrderTypeError (Info, Option Type)
  --   | DTCTypeConstraintErrorR (Info, Option (DTCReg, Type))
  | DTCPartiallyAppliedConst (Info, Option Const)

  sem typeErrorInfo : DTCTypeError -> Info
  sem typeErrorInfo =
  | DTCTypeError i -> i
  | DTCArrowError (i, _)
  | DTCArgError (i, _)
  | DTCJoinError (i, _)
  | DTCPatError (i, _)
  | DTCAnotError i
  --   | DTCSolveODEModelError (i, _)
  | DTCDiffFnError (i, _)
  | DTCDiffFnNotRnError (i, _)
  | DTCPolyDistError i
  | DTCPolyConstError i
  | DTCUnuspportedTermError (i, _)
  | DTCInvalidContextError (i, _) -> i
  --   | DTCContextConstraintError (i, _) -> i
  --   | DTCHigherOrderTypeError (i, _) -> i
  --   | DTCTypeConstraintErrorR (i, _) -> i
  | DTCPartiallyAppliedConst (i, _) -> i

  sem typeErrorToString : DTCTypeError -> String
  sem typeErrorToString =
  | DTCTypeError _ -> "TypeError"
  | DTCArrowError _ -> "ArrowError"
  | DTCArgError _ -> "ArgError"
  | DTCJoinError _ -> "JoinError"
  | DTCPatError _ -> "PatError"
  | DTCAnotError _ -> "AnotError"
  --   | DTCSolveODEModelError _ -> "SolveODEModelError"
  | DTCDiffFnError _ -> "DiffFnError"
  | DTCDiffFnNotRnError _ -> "DiffFnNotRnError"
  | DTCPolyDistError _ -> "PolyDistError"
  | DTCPolyConstError _ -> "PolyConstError"
  | DTCUnuspportedTermError _ -> "UnuspportedTermError"
  | DTCInvalidContextError _ -> "InvalidContextError"
  --   | DTCContextConstraintError _ -> "ContextConstraintError"
  --   | DTCHigherOrderTypeError _ -> "HigherOrderTypeError"
  --   | DTCTypeConstraintErrorR _ -> "TypeConstraintErrorR"
  | DTCPartiallyAppliedConst _ -> "PartiallyAppliedConst"

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
    (info, join
             [ "* Cannot join: ", type2str ty1, "\n"
             , "*       with: ", type2str ty2
             ])
  | DTCPatError (info, Some ty) ->
    (info, join ["* Pattern does not match type: ", type2str ty])
  | DTCAnotError info ->
    (info, join ["* Missing type annotation"])
--   | DTCSolveODEModelError (info, Some ty) ->
--     (info,
--      _typeErrorToMsg2
--        ["Determinstic function type FloatX -> T[Y] -> T,",
--         join [
--           "where T isomorfic to a vector of floats, and X = ",
--           dtcRegToString (ModA ()), " or X = ",
--           dtcRegToString (ModC ()),
--           ", and Y = ",
--           dtcRegToString (ModA ()),
--           "." ]]
--        [type2str ty])
  | DTCDiffFnError (info, Some (c, ty)) ->
    (info,
     _typeErrorToMsg2
       [ "Determinstic function isomorfic to:"
       , "FloatAⁿ ->{M,P,A} FloatAᵐ or FloatPⁿ ->{P} FloatPᵐ"
       ]
       [type2str ty])
  | DTCDiffFnError (info, Some ty) ->
    (info,
     _typeErrorToMsg2 [ "Function isomorfic to Floatⁿ -> Floatᵐ"]
       [type2str ty])
  | DTCPolyDistError info ->
    (info, "* Polymorfic distributions are currently not supported")
  | DTCPolyConstError info ->
    (info, join
             [ "* Cannot infer the type of this polymorphic intrinsic.\n"
             , "* Try to apply it to one or more arguments."
             ])
  | DTCUnuspportedTermError (info, Some tm) ->
    dprint tm;
    (info, strJoin "\n" ["* This term is currently not supported:", expr2str tm])
  | DTCInvalidContextError (info, Some name) ->
    (info, join
             [ "* The variable ", nameGetStr name
             , " does not appear in the typing context.\n"
             , "* This should not happen in symbolized progams."
             ])
--   | DTCContextConstraintError (info, Some (c, env)) ->
--     (info, join [
--       "* The type context ", dtcEnvToString env, "\n",
--       "* is not less than or equal to ", dtcRegToString c
--     ])
--   | DTCHigherOrderTypeError (info, Some ty) ->
--     (info, join [
--       "* A higher order type is not allowed here but got:\n",
--       type2str ty
--     ])
--   | DTCTypeConstraintErrorR (info, Some (c, ty)) ->
--     (info, join [
--       "* Type constriant error: ",
--       dtcRegToString c, " ≤ ",
--       type2str ty,
--       " does not hold."
  --     ])
  | DTCPartiallyAppliedConst (info, Some const) ->
    (info, join ["* Partially applied ", getConstStringCode 0 const])
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
  type DTCTypeResult a = Result DTCTypeError DTCTypeError a
  type DTCType = {e : DTCEffect, ty : Type, fv : Set Name}

  sem typeOfH : DTCEnv -> Expr -> DTCTypeResult DTCType
  sem typeOfH env =| tm ->
    result.err (DTCUnuspportedTermError (infoTm tm, Some tm))

  sem resultOK : [DTCEffect] -> Type -> [Set Name] -> DTCTypeResult DTCType
  sem resultOK es ty =| fvs ->
    result.ok { e = foldr1 dtcMule es, ty = ty, fv = foldr1 setUnion fvs }

  sem argErr : all a. Expr -> Type -> Type -> Result DTCTypeError DTCTypeError a
  sem argErr tm ty1 =| ty2 ->
    result.err (DTCArgError (infoTm tm, Some (ty1, ty2)))

  sem typeOf : DTCEnv -> Expr -> DTCTypeResult (DTCEffect, Type)
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
    DTCTypeResult ((DTCEffect, Set Name), [Type])
  sem mapAccumLTypeOfH env =| tms ->
    result.bind (result.mapM (typeOfH env) tms) (lam rs.
      result.ok
        (mapAccumL
           (lam acc. lam r.
             match acc with (e, fv) in
             ((dtcMule e r.e, setUnion fv r.fv), r.ty))
           (ModD (), setEmpty nameCmp)
           rs))

  -- Accumulates effects and free variables.
  sem foldTypeOfH :
    DTCEnv ->
      DTCTypeResult {e : DTCEffect, fv : Set Name} ->
        Expr ->
          DTCTypeResult {e : DTCEffect, fv : Set Name}
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
      (lam ty. result.ok
               { e = ModD ()
               , ty = ty
               , fv = setSingleton nameCmp r.ident
               })
      (dtcEnvLookup r.ident env)
end

lang DTCTypeOfLam = LamAst + DTCTypeOfBase
  sem typeOfH env =
  | TmLam (r &
    {tyAnnot = TyUnknown _}) ->
    result.err (DTCAnotError r.info)
  | TmLam r ->
    result.bind (typeOfH (dtcEnvInsert r.ident r.tyAnnot env) r.body)
      (lam body.
        let fv = setRemove r.ident body.fv in
        let cs = dtcEnvAccPromote (dtcEnvWeaken fv env) in
        result.ok
          { e = ModD ()
          , ty = ityarrowXe_ r.info r.tyAnnot body.ty cs body.e
          , fv = fv
          })
end

lang DTCTypeOfApp = AppAst + DTCFunTypeAst + FreeVars + DTCTypeOfBase
  sem typeOfH env =
  | TmApp r ->
    result.bind (typeOfH env r.lhs) (lam lhs.
      match lhs with {ty = TyArrowCE arr} then
        result.bind (typeOfH env r.rhs) (lam rhs.
          if subtype rhs.ty arr.from then
            let fv = setUnion lhs.fv rhs.fv in
            let cs = accApp (dtcEnvAccPromote (dtcEnvWeaken fv env)) arr.to in
            resultOK [lhs.e, rhs.e] (mulXType cs arr.to) [fv]
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

lang DTCTyConst = TyConst + DTCTypeError + DTCTypeOfBase + ConstArity
  sem dtcConstType : Info -> (Const, [Type]) -> DTCTypeResult Type
  sem dtcConstType info =
  | (const, _) ->
    let ty = fromMExprTy (tyConst const) in
    match ty with TyAll _ then result.err (DTCPolyConstError info)
    else result.ok ty
end

lang DTCTypeOfConst =
  ConstAst + AppAst + DTCTyConst + CmpFloatAst + ElementaryFunctions +
  DTCFunTypeAst + DTCTypeOfBase

  sem effecIfApplied : Type -> DTCEffect
  sem effecIfApplied =
  | TyArrowCE {e = ModR _} -> ModR ()
  | TyArrowCE r -> effecIfApplied r.to
  | _ -> ModD ()

  sem typeOfConstApp0 : Info -> Const -> DTCTypeResult DTCType
  sem typeOfConstApp0 info =| const ->
    if eqi (constArity const) 0 then
      result.bind (dtcConstType info (const, []))
        (lam ty. result.ok
                 { e = ModD ()
                 , ty = ty
                 , fv = setEmpty nameCmp
                 })
    else result.err (DTCPartiallyAppliedConst (info, Some const))

  sem typeOfConstApp1 : DTCEnv -> Info -> (Const, Expr) -> DTCTypeResult DTCType
  sem typeOfConstApp1 env info =| (const, tm) ->
    if eqi (constArity const) 1 then
      result.bind (typeOfH env tm)
        (lam tm.
          result.bind (dtcConstType info (const, [tm.ty])) (lam constTy.
            match constTy with TyArrowCE r then
              if subtype tm.ty r.from then
                let cs =
                  accApp (dtcEnvAccPromote (dtcEnvWeaken tm.fv env)) r.to in
                result.ok
                  { e = dtcMule (effecIfApplied tm.ty) tm.e
                  , ty = mulXType cs r.to
                  , fv = tm.fv
                  }
              else result.err (DTCArgError (info, Some (r.from, tm.ty)))
            else error "typeOfConstApp1: impossible"))
    else result.err (DTCPartiallyAppliedConst (info, Some const))

  sem typeOfConstApp2 : DTCEnv -> Info -> (Const, Expr, Expr) -> DTCTypeResult DTCType
  sem typeOfConstApp2 env info =| (const, tm1, tm2) ->
    if eqi (constArity const) 2 then
      result.bind2 (typeOfH env tm1) (typeOfH env tm2)
        (lam tm1. lam tm2.
          result.bind (dtcConstType info (const, [tm1.ty, tm2.ty])) (lam constTy.
            match constTy with TyArrowCE (r1 & {to = TyArrowCE r2}) then
              if subtype tm1.ty r1.from then
                if subtype tm2.ty r2.from then
                  let fv = setUnion tm1.fv tm2.fv in
                  let cs =
                    accApp (dtcEnvAccPromote (dtcEnvWeaken fv env)) r2.to in
                  result.ok
                    { e = foldl1 dtcMule
                            (concat (map effecIfApplied [tm1.ty, tm2.ty])
                               [tm1.e, tm2.e])
                    , ty = mulXType cs r2.to
                    , fv = fv
                    }
                else result.err (DTCArgError (info, Some (r2.from, tm2.ty)))
              else result.err (DTCArgError (info, Some (r1.from, tm1.ty)))
            else error "typeOfConstApp2: impossible"))
    else result.err (DTCPartiallyAppliedConst (info, Some const))

  sem typeOfConstApp3 : DTCEnv -> Info -> (Const, Expr, Expr, Expr) ->
    DTCTypeResult DTCType
  sem typeOfConstApp3 env info =| (const, tm1, tm2, tm3) ->
    if eqi (constArity const) 3 then
      result.bind3 (typeOfH env tm1) (typeOfH env tm2) (typeOfH env tm3)
        (lam tm1. lam tm2. lam tm3.
          result.bind (dtcConstType info (const, [tm1.ty, tm2.ty, tm3.ty]))
            (lam constTy.
              match constTy with
                TyArrowCE (r1 & {to = TyArrowCE (r2 & {to = TyArrowCE r3})})
              then
                if subtype tm1.ty r1.from then
                  if subtype tm2.ty r2.from then
                    if subtype tm3.ty r3.from then
                      let fv = setUnion (setUnion tm1.fv tm2.fv) tm3.fv in
                      let cs =
                        accApp (dtcEnvAccPromote (dtcEnvWeaken fv env)) r3.to in
                      result.ok
                        { e = foldl1 dtcMule
                                (concat
                                   (map effecIfApplied [tm1.ty, tm2.ty, tm2.ty])
                                   [tm1.e, tm2.e, tm3.e])
                        , ty = mulXType cs r3.to
                        , fv = fv
                        }
                    else result.err (DTCArgError (info, Some (r3.from, tm3.ty)))
                  else result.err (DTCArgError (info, Some (r2.from, tm2.ty)))
                else result.err (DTCArgError (info, Some (r1.from, tm1.ty)))
              else error "typeOfConstApp3: impossible"))
    else result.err (DTCPartiallyAppliedConst (info, Some const))

  sem typeOfH env =
  | TmConst r ->
    typeOfConstApp0 r.info r.val
  | TmApp {lhs = TmConst r, rhs = tm, info = i} ->
    typeOfConstApp1 env i (r.val, tm)
  | TmApp {lhs = TmApp {lhs = TmConst r, rhs = tm1}, rhs = tm2, info = i} ->
    typeOfConstApp2 env i (r.val, tm1, tm2)
  | TmApp
    {lhs = TmApp {lhs = TmApp{lhs = TmConst r, rhs = tm1}, rhs = tm2}
    ,rhs = tm3, info = i
    } -> typeOfConstApp3 env i (r.val, tm1, tm2, tm3)
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
                 (joinType ty1 ty2))
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
    DTCTypeResult (Map Name Type)
  sem dtcTypeCheckPat env patEnv =| (ty, pat) ->
    result.err (DTCPatError (infoPat pat, Some ty))

  sem dtcTypeCheckPatSeq : DTCEnv -> Map Name Type -> [(Type, Pat)] ->
    DTCTypeResult (Map Name Type)
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
    result.bind (typeOfH env r.target) (lam target.
      result.bind
        (dtcTypeCheckPat env (mapEmpty nameCmp) (target.ty, r.pat))
        (lam patEnv.
          let thnEnv = dtcEnvBatchInsert patEnv env in
          result.bind2 (typeOfH thnEnv r.thn) (typeOfH env r.els)
            (lam thn. lam els.
              optionMapOr
                (result.err (DTCJoinError (r.info, Some (thn.ty, els.ty))))
                (lam ty.
                  resultOK [target.e, thn.e, els.e] ty [
                    target.fv,
                    setSubtract thn.fv (setOfKeys patEnv),
                    els.fv ])
                (joinType thn.ty els.ty))))
--  | TmMatch r -> typeOfBoolStrict env r

--   -- NOTE(oerikss, 2025-10-14): We need stricter typing if it is possible that
--   -- the match includes a condition on floating point values.
--   sem typeOfBoolStrict env =
--   | r ->
--     result.bind (typeOfHPromote env r.target) (lam target.
--       result.bind
--         (dtcTypeCheckPat env (mapEmpty nameCmp) (target.ty, r.pat))
--         (lam patEnv.
--           let thnEnv = dtcEnvBatchInsert patEnv env in
--           result.bind2 (typeOfHPromote thnEnv r.thn) (typeOfHPromote env r.els)
--             (lam thn. lam els.
--               if isFirstOrder thn.ty then
--                 if isFirstOrder els.ty then
--                   optionMapOr
--                     (result.err (DTCJoinError (r.info, Some (thn.ty, els.ty))))
--                     (lam ty.
--                       let tyP = setC (ModP ()) ty in
--                       optionMapOr
--                         (result.err (DTCJoinError (r.info, Some (tyP, ty))))
--                         (lam ty.
--                           resultOK [target.e, thn.e, els.e] ty [
--                             target.fv,
--                             setSubtract thn.fv (setOfKeys patEnv),
--                             els.fv ])
--                         (joinType (ty, tyP)))
--                     (joinType (thn.ty, els.ty))
--                 else
--                   result.err
--                     (DTCHigherOrderTypeError (infoTm r.els, Some els.ty))
--               else
--                 result.err
--                   (DTCHigherOrderTypeError (infoTm r.thn, Some thn.ty)))))
end

lang DTCTypeOfInfer = Infer + DTCTypeOfBase
  sem typeOfH env =
  | TmInfer r ->
    result.bind2
      (inferSfold_Expr_Expr
         (foldTypeOfH env)
         (result.ok { e = ModD (), fv = setEmpty nameCmp }) r.method)
      (typeOfH env r.model)
      (lam method. lam model.
        let err =
          argErr r.model
            (tyarrowXe_ tyunit_ (tyvar_ "a") [] (ModR ())) model.ty
        in
        match model with {ty = TyArrowCE (arr & {from = TyRecord rr})} then
          let ty = tyarrowXe_ tyunit_ arr.to [] (ModR ()) in
          if subtype model.ty ty then
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
      match dist with {ty = TyDist _} then
        let cs =
          accApp (dtcEnvAccPromote (dtcEnvWeaken dist.fv env)) dist.ty in
        result.ok { dist with e = ModR (), ty = mulXType cs dist.ty }
      else
        result.err
          (DTCArgError
            (infoTm r.dist, Some (tydist_ (tyvar_ "a"), dist.ty))))
end

lang DTCTypeOfObserve = Observe + DTCTypeOfBase
  sem typeOfH env =
  | TmObserve r ->
    result.bind2 (typeOfH env r.value) (typeOfH env r.dist)
      (lam value. lam dist.
        match dist with {ty = TyDist {ty = suppTy}} then
          if subtype value.ty suppTy then
            resultOK [value.e, dist.e] (tyWithInfo r.info tyunit_)
              [value.fv, dist.fv]
          else argErr r.value value.ty suppTy
        else argErr r.dist dist.ty (tydist_ value.ty))
end

lang DTCTypeOfWeight = Weight + DTCTypeOfBase
  sem typeOfH env =
  | TmWeight r ->
    result.bind (typeOfH env r.weight) (lam weight.
      let ty = tyfloatX_ [] in
      if subtype weight.ty ty then
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
               if uncurry subtype t then result.ok ()
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
         , ityarrowXe_ info (tyfloatc_ (ModC ())) (tyfloatc_ (ModA ()))
             [] (ModD ()) )
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
      (typeOfH env r.fn) (typeOfH env r.arg) (typeOfH env r.darg)
      (lam fn. lam arg. lam darg.
        let err = lam.
          result.err (DTCDiffFnError (infoTm r.fn, Some (ModP (), fn.ty))) in
        match fn.ty with TyArrowCE arr then
          if and (isIsomorficToRn arr.from) (isIsomorficToRn arr.to) then
            let withA = withX (dtcXDown (ModA ())) in
            let fv = foldl1 setUnion [fn.fv, arg.fv, darg.fv] in
            let cs =
              foldl accApp
                (dtcEnvAccPromote (dtcEnvWeaken fv env))
                [fn.ty, arg.ty, darg.ty] in
            let ok = lam.
              result.ok
                { fv = fv
                , ty = mulXType cs (withA arr.to)
                , e = foldl1 dtcMule [fn.e, arg.e, darg.e]
                } in
            if subtype arg.ty (withA arr.from) then
              if subtype darg.ty (withA arr.from) then
                if subtype fn.ty
                     (tyarrowXe_
                        (withA arr.from) (withA arr.to)
                        [ModP (), ModA ()]
                        (ModD ()))
                then ok ()
                else
                  let withP = withX (dtcXDown (ModP ())) in
                  if subtype fn.ty
                       (tyarrowXe_
                          (withP arr.from) (withP arr.to)
                          [ModP ()]
                          (ModD ()))
                  then ok ()
                  else err ()
              else
                result.err
                  (DTCArgError (infoTm r.darg, Some (withA arr.from, darg.ty)))
            else
              result.err
                (DTCArgError (infoTm r.arg, Some (withA arr.from, arg.ty)))
          else result.err (DTCDiffFnNotRnError (infoTm r.fn, Some (fn.ty)))
        else err ())
end

-- -- lang DTCTypeOfSolveODE = SolveODE + IsIsomorficToRn + DTCTypeOfBase
-- --   -- sem typeOfH env =
-- --   -- | TmSolveODE r ->
-- --   --   result.bind4
-- --   --     (sfold_ODESolverMetod_Expr
-- --   --        (foldTypeOfH env)
-- --   --        (result.ok { e = ModD (), fv = setEmpty nameCmp }) r.method)
-- --   --     (typeOfH env r.model)
-- --   --     (typeOfH env r.init)
-- --   --     (typeOfH env r.endTime)
-- --   --     (lam method. lam model. lam init. lam x1.
-- --   --       match model.ty with
-- --   --         TyArrowCE (arr1 & {
-- --   --           from = TyFloatC {c = c & (ModA _ | ModC _)},
-- --   --           to = TyArrowCE (arr2 & {e = ModD _}), e = ModD _})
-- --   --       then
-- --   --         if isIsomorficToRn arr2.from then
-- --   --           let xTy = arr1.from in
-- --   --           let yTy = setC (ModA ()) arr2.from in
-- --   --           let odeRhsTy =
-- --   --             TyArrowCE {
-- --   --               arr1 with to = tyarrowce_ yTy yTy (ModA ()) (ModD ()),
-- --   --               c = ModC ()
-- --   --             }
-- --   --           in
-- --   --           let x1Ty = mulcType (ModPC ()) xTy in
-- --   --           let fv =
-- --   --             foldr1 setUnion [method.fv, model.fv, init.fv, x1.fv]
-- --   --           in
-- --   --           let promote = promote env fv in
-- --   --           if subtype (model.ty, odeRhsTy) then
-- --   --             if subtype (init.ty, tytuple_ [xTy, yTy]) then
-- --   --               if subtype (x1.ty, x1Ty) then
-- --   --                 resultOK [method.e, model.e, init.e, x1.e]
-- --   --                   (promote (setC (ModA ()) (tytuple_ [xTy, yTy]))) [fv]
-- --   --               else argErr r.endTime x1.ty x1Ty
-- --   --             else
-- --   --               argErr r.init init.ty (tytuple_ [xTy, yTy])
-- --   --           else
-- --   --             result.err
-- --   --               (DTCArgError (infoTm r.model, Some (odeRhsTy, model.ty)))
-- --   --         else
-- --   --           result.err
-- --   --             (DTCSolveODEModelError (infoTm r.model, Some model.ty))
-- --   --       else
-- --   --         result.err
-- --   --           (DTCSolveODEModelError (infoTm r.model, Some model.ty)))
-- -- end

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
  use DTCAst in ityarrowXe_ info from to [] (ModD ())

let arr_ = lam from. lam to.
  use DTCAst in ityarrowXe_ (NoInfo ()) from to [] (ModD ())

let iarre_ = lam info. lam from. lam to. lam e.
  use DTCAst in ityarrowXe_ info from to [] e

lang DTCFloatType = DTCTyConst
  sem dtcConstType info =| (CFloat _, []) ->
    result.ok (ityfloatX_ info [])
end

-- NOTE(oerikss, 2025-10-08): We assume that elementary functions are analytic
-- and defined on the whole real number line. Evaluation at undefined inputs
-- will result in runtime errors.

lang DTCArithFloatType = ArithFloatAst + DTCTyConst
  sem dtcConstType info =
  | (CAddf _ | CSubf _ | CMulf _, _) ->
    let tyfloat = ityfloatc_ info (ModA ()) in
    let arr = lam from. lam to. iarr_ info from to in
    result.ok (arr tyfloat (arr tyfloat tyfloat))
  | (CDivf _, _) ->
    let tyfloat = lam c. ityfloatc_ info c in
    let arr = lam from. lam to. iarr_ info from to in
    result.ok
      (arr (tyfloat (ModA ()))
         (arr (tyfloat (ModP ())) (tyfloat (ModA ()))))
  | (CNegf _, _) ->
    let tyfloat = ityfloatc_ info (ModA ()) in
    result.ok (iarr_ info tyfloat tyfloat)
end

lang DTCElementaryFunctionsType = ElementaryFunctions + DTCTyConst
  sem dtcConstType info =
  | (CSin _ | CCos _ | CExp _, _) ->
    let tyfloat = ityfloatc_ info (ModA ()) in
    result.ok (iarr_ info tyfloat tyfloat)
  | (CLog _ | CSqrt _  | CAbsf _, _) ->
    let tyfloat = ityfloatc_ info (ModP ()) in
    result.ok (iarr_ info tyfloat tyfloat)
  | (CAbsf _, _) ->
    let tyfloat = ityfloatX_ info dtcPC in
    result.ok (iarr_ info tyfloat tyfloat)
  | (CPow _, _) ->
    let tyfloat = ityfloatc_ info (ModA ()) in
    let arr = lam from. lam to. iarr_ info from to in
    result.ok (arr tyfloat (arr tyfloat tyfloat))
end

lang DTCCmpFloatAstType = CmpFloatAst + DTCTyConst
  sem dtcConstType info =
  | (CEqf _ | CLtf _ | CLeqf _ | CGtf _ | CGeqf _ | CNeqf _, _) ->
    let tyfloatp = ityfloatc_ info (ModP ()) in
    let arr = lam from. lam to. iarr_ info from to in
    result.ok (arr tyfloatp (arr tyfloatp (itybool_ info)))
end

let _a = tyvar_ "a"
let _b = tyvar_ "b"

lang DTCSysType = SysAst + DTCTypeOfConst
  sem dtcConstType info =
  | (CExit _, _) -> result.ok (TyBot { info = info })
  | (CError _, _) ->
    result.ok (iarr_ info (itystr_ info) (TyBot { info = info }))
end

lang DTCSeqOpType = SeqOpAst + DTCTypeOfConst
  sem dtcConstType info =
  | (CSet _, [TySeq seqr, _, elty]) ->
    optionMapOr (result.err (DTCPolyConstError info))
      (lam elty.
        let arr = foldr1 (iarr_ info) in
        let tyseq = TySeq { seqr with ty = elty } in
        result.ok (arr [tyseq, ityint_ info, elty, tyseq]))
      (joinType seqr.ty elty)
  | (CGet _, [tyseq & TySeq seqr, _]) ->
    let arr = foldr1 (iarr_ info) in
    result.ok (arr [tyseq, ityint_ info, seqr.ty])
  | (CCons _, [elty, TySeq seqr]) ->
    optionMapOr (result.err (DTCPolyConstError info))
      (lam elty.
        let arr = foldr1 (iarr_ info) in
        let tyseq = TySeq { seqr with ty = elty } in
        result.ok (arr [elty, tyseq, tyseq]))
      (joinType elty seqr.ty)
  | (CSnoc _, [TySeq seqr, elty]) ->
    optionMapOr (result.err (DTCPolyConstError info))
      (lam elty.
        let arr = foldr1 (iarr_ info) in
        let tyseq = TySeq { seqr with ty = elty } in
        result.ok (arr [tyseq, elty, tyseq]))
      (joinType seqr.ty elty)
  | (CConcat _, [TySeq seqr1, TySeq seqr2]) ->
    optionMapOr (result.err (DTCPolyConstError info))
      (lam elty.
        let arr = foldr1 (iarr_ info) in
        let tyseq = TySeq { seqr1 with ty = elty } in
        result.ok (arr [tyseq, tyseq, tyseq]))
      (joinType seqr1.ty seqr2.ty)
  | (CLength _, [tyseq & TySeq _]) ->
    let arr = foldr1 (iarr_ info) in
    result.ok (arr [tyseq, ityint_ info])
  | (CReverse _, [tyseq & TySeq _]) ->
    let arr = foldr1 (iarr_ info) in result.ok (arr [tyseq, tyseq])
  | (CHead _, [tyseq & TySeq seqr]) ->
    let arr = foldr1 (iarr_ info) in result.ok (arr [tyseq, seqr.ty])
  | (CTail _, [tyseq & TySeq _]) ->
    let arr = foldr1 (iarr_ info) in result.ok (arr [tyseq, tyseq])
  | (CNull _ | CIsList _ | CIsRope _, [tyseq & TySeq _]) ->
    let arr = foldr1 (iarr_ info) in result.ok (arr [tyseq, itybool_ info])
  | (CMap _, [tyarr & TyArrowCE arrr, TySeq seqr]) ->
    let arr = foldr1 (iarr_ info) in
    result.ok
      (arr
         [ tyarr
         , TySeq { seqr with ty = arrr.from }
         , TySeq { seqr with ty = arrr.to }
         ])
  | (CMapi _, [TyArrowCE (arrr1 & {to = TyArrowCE arrr2}), TySeq seqr]) ->
    let arr = foldr1 (iarr_ info) in
    result.ok
      (arr
         [ TyArrowCE { arrr1 with from = ityint_ info }
         , TySeq { seqr with ty = arrr2.from }
         , TySeq { seqr with ty = arrr2.to }
         ])
  | (CIter _, [TyArrowCE arrr, TySeq seqr]) ->
    let arr = foldr1 (iarr_ info) in
    result.ok
      (arr
         [ TyArrowCE { arrr with to = tyunit_ }
         , TySeq { seqr with ty = arrr.from }
         , tyunit_
         ])
  | (CIteri _, [TyArrowCE (arrr1 & {to = TyArrowCE arrr2}), TySeq seqr]) ->
    let arr = foldr1 (iarr_ info) in
    result.ok
      (arr
         [ TyArrowCE
           { arrr1 with from = ityint_ info
           , to = TyArrowCE { arrr2 with to = tyunit_ }
           }
         , TySeq { seqr with ty = arrr2.from }
         , tyunit_
         ])
  | (CFoldl _
    ,[TyArrowCE (arrr1 & {to = TyArrowCE arrr2}), _, TySeq seqr]) ->
    let arr = foldr1 (iarr_ info) in
    result.ok
      (arr
         [ TyArrowCE { arrr1 with to = TyArrowCE { arrr2 with to = arrr1.from }}
         , arrr1.from
         , TySeq { seqr with ty = arrr2.from }
         , arrr1.from
         ])
  | (CFoldr _
    ,[TyArrowCE (arrr1 & {to = TyArrowCE arrr2}), _, TySeq seqr]) ->
    let arr = foldr1 (iarr_ info) in
    result.ok
      (arr
         [ TyArrowCE { arrr1 with to = TyArrowCE { arrr2 with to = arrr2.from }}
         , arrr2.from
         , TySeq { seqr with ty = arrr1.from }
         , arrr2.from
         ])
  | (CCreate _ | CCreateList _ | CCreateRope _, [_, TyArrowCE arrr]) ->
    let arr = foldr1 (iarr_ info) in
    result.ok
      (arr
         [ ityint_ info
         , TyArrowCE { arrr with from = ityint_ info }
         , ityseq_ info arrr.to
         ])
  | (CSplitAt _, [tyseq & TySeq seqr, _]) ->
    let arr = foldr1 (iarr_ info) in
    result.ok (arr [tyseq, ityint_ info, itytuple_ info [tyseq, tyseq]])
  | (CSubsequence _, [tyseq & TySeq seqr, _, _]) ->
    let arr = foldr1 (iarr_ info) in
    result.ok (arr [tyseq, ityint_ info, ityint_ info, tyseq])
end

-- lang DTCDistOpType = Dist + DTCTypeOfConst
--   -- Type-checks polymorfic constant functions over distributions
--
--   sem _distargerr tm =| ty ->
--     result.err (DTCArgError (infoTm tm, Some (tydist_ _a, ty)))
--
--   sem typeOfH env =
--   | TmApp (r & {lhs = TmConst {val = CDistEmpiricalSamples _}}) ->
--     result.bind (typeOfH env r.rhs) (lam rhs.
--       match rhs with {ty = TyDist distr} then
--         let seq = ityseq_ r.info in
--         result.ok {
--           rhs with ty = itytuple_ r.info [
--             seq distr.ty, seq (ityfloatc_ r.info (ModM ()))]
--         }
--       else _distargerr r.rhs rhs.ty)
--   | TmApp (r & {lhs = TmConst {val = CDistEmpiricalDegenerate _}}) ->
--     result.bind (typeOfH env r.rhs) (lam rhs.
--       match rhs with {ty = TyDist _} then
--         result.ok { rhs with ty = itybool_ r.info }
--       else _distargerr r.rhs rhs.ty)
--   | TmApp (r & {lhs = TmConst {
--     val = CDistEmpiricalNormConst _ | CDistEmpiricalAcceptRate _ }}) ->
--     result.bind (typeOfH env r.rhs) (lam rhs.
--       match rhs with {ty = TyDist _} then
--         result.ok { rhs with ty = ityfloatc_ r.info (ModM ()) }
--       else _distargerr r.rhs rhs.ty)
-- end

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
           (joinType patTy ty))
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
  DTCTypeOfDist + DTCTypeOfDiff +
  -- DTCTypeOfSolveODE +
  TypeOfUtest +

  -- Constants
  DTCTyConst + DTCFloatType + DTCArithFloatType + DTCElementaryFunctionsType +
  DTCCmpFloatAstType + DTCSysType + DTCSeqOpType +

  -- DTCDistOpType +

  -- Patterns
  DTCPatTypeCheckAll
end

lang TestLang = DTCAst + DTCTypeOf + MExprPPL end

mexpr

use TestLang in

-- Define some shorthand names.

let _D  = ModD () in
let _R  = ModR () in

let _A  = ModA () in
let _P  = ModP () in
let _C  = ModC () in

-- ┌────────────┐
-- │ TEST TYPES │
-- └────────────┘

let applyBoth = lam p. lam x. lam y. (p x y, p y x) in
let dup = lam x. (x, x) in
let cartesian = lam f. lam xs. lam ys. map (lam x. map (f x) ys) xs in

let pairToString : all a. (a -> String) -> (a, a) -> String =
  lam f. lam t. join [f t.0, "\n", f t.1] in

let matrixToString = lam r : [String]. lam c : [String]. lam f. lam m.
  let maxlen =
    optionGetOrElse (lam. error "duh!")
      (max subi (map length (join [r, c, map f (join m)]))) in
  let pad = lam str.
    let diff = subi maxlen (length str) in
    if eqi diff 0 then str
    else concat str (create diff (lam. ' ')) in
  concat
    (snoc (strJoin ", " (map pad c)) '\n')
    (strJoin "\n"
       (mapi
          (lam i. lam x.
            join
              [ pad (get r i), ": "
              , strJoin ", " (map (lam x. pad (f x)) x)
              ])
          m)) in

let eqMatrix = lam cmp. lam x. lam y.
  allb [ eqi (length x) (length y)
       , eqi (length (join x)) (length (join y))
       , allb ((zipWith cmp (join x) (join y))) ] in

let _eqJoin    = tupleEq2 (optionEq eqType) (optionEq eqType) in
let _toStrJoin =
  let f = pairToString (optionMapOr "None" type2str) in
  utestDefaultToString f f in

let _eqMeet    = tupleEq2 eqType eqType in
let _toStrMeet =
  let f = pairToString type2str in
  utestDefaultToString f f in

-- ┌────────────┐
-- │ Test TyBot │
-- └────────────┘

-- Utils

utest eqType tybot_ tybot_ with true in
utest applyBoth eqType tybot_ tyunknown_ with (false, false) in

utest eraseDecorationsType tybot_ with tyunknown_ using eqType in

-- Subtyping

utest applyBoth subtype tybot_ tyunknown_ with (true, false) in

utest applyBoth joinType tybot_ tyunknown_ with dup (Some tyunknown_)
  using _eqJoin in

utest applyBoth meetType tybot_ tyunknown_ with dup tybot_ using _eqMeet in

-- ┌───────────────┐
-- │ Test TyFloatC │
-- └───────────────┘

-- Utils

utest cartesian (lam c. lam d. eqType (tyfloatc_ c) (tyfloatc_ d)) dtcReg dtcReg with
  [ [true,  false, false]
  , [false, true,  false]
  , [false, false, true]
  ] in

utest map (lam c. eraseDecorationsType (tyfloatc_ c)) dtcReg
  with create 3 (lam. tyfloat_)
  using eqSeq eqType in

-- Subtyping

let allValidFloatTys =
  join [[tyfloatX_ []], map (lam c. tyfloatc_ c) dtcReg, [tyfloatX_ dtcPC]] in

let tys = snoc allValidFloatTys tyunknown_ in
let lbls = ["{}", "C", "P", "A", "PC", "Ukn"] in
let _matrixToString =
  matrixToString lbls (cons "  " lbls) (lam x. if x then "T" else "F") in

utest cartesian subtype tys tys with
  -- {}      C      P      A      PC     Ukn
  [ [true,  true,  true,  true,  true,  false]    -- {}
  , [false, true,  false, true,  true,  false]    -- C
  , [false, false, true,  true,  true,  false]    -- P
  , [false, false, false, true,  false, false]    -- A
  , [false, false, false, true,  true,  false]    -- PC
  , [false, false, false, false, false, true]     -- Ukn
  ]
  using eqMatrix eqBool
else utestDefaultToString _matrixToString _matrixToString in

let _matrixToString =
  matrixToString lbls (cons "  " lbls) (optionMapOr "None" type2str) in

utest cartesian joinType tys tys with
  -- {}                       C                       P                       A                    PC                      Ukn
  [ [Some (tyfloatX_ []),    Some (tyfloatc_ _C),    Some (tyfloatc_ _P),    Some (tyfloatc_ _A), Some (tyfloatX_ dtcPC), None ()]         -- {}
  , [Some (tyfloatc_ _C),    Some (tyfloatc_ _C),    Some (tyfloatX_ dtcPC), Some (tyfloatc_ _A), Some (tyfloatX_ dtcPC), None ()]         -- C
  , [Some (tyfloatc_ _P),    Some (tyfloatX_ dtcPC), Some (tyfloatc_ _P),    Some (tyfloatc_ _A), Some (tyfloatX_ dtcPC), None ()]         -- P
  , [Some (tyfloatc_ _A),    Some (tyfloatc_ _A),    Some (tyfloatc_ _A),    Some (tyfloatc_ _A), Some (tyfloatc_ _A),    None ()]         -- A
  , [Some (tyfloatX_ dtcPC), Some (tyfloatX_ dtcPC), Some (tyfloatX_ dtcPC), Some (tyfloatc_ _A), Some (tyfloatX_ dtcPC), None ()]         -- PC
  , [None (),                None (),                None (),                None (),             None (),                Some tyunknown_] -- Ukn
  ]
  using eqMatrix (optionEq eqType)
else utestDefaultToString _matrixToString _matrixToString in

let _matrixToString =
  matrixToString lbls (cons "  " lbls) type2str in

utest cartesian meetType tys tys with
  -- {}             C             P             A                PC               Ukn
  [ [tyfloatX_ [], tyfloatX_ [], tyfloatX_ [], tyfloatX_ [],    tyfloatX_ [],    tybot_]         -- {}
  , [tyfloatX_ [], tyfloatc_ _C, tyfloatX_ [], tyfloatc_ _C,    tyfloatc_ _C,    tybot_]         -- C
  , [tyfloatX_ [], tyfloatX_ [], tyfloatc_ _P, tyfloatc_ _P,    tyfloatc_ _P,    tybot_]         -- P
  , [tyfloatX_ [], tyfloatc_ _C, tyfloatc_ _P, tyfloatc_ _A,    tyfloatX_ dtcPC, tybot_]         -- A
  , [tyfloatX_ [], tyfloatc_ _C, tyfloatc_ _P, tyfloatX_ dtcPC, tyfloatX_ dtcPC, tybot_]         -- PC
  , [tybot_,       tybot_,       tybot_,       tybot_,          tybot_,          tyunknown_]     -- Ukn
  ]
  using eqMatrix eqType
else utestDefaultToString _matrixToString _matrixToString in

-- ┌────────────────┐
-- │ Test TyArrowCE │
-- └────────────────┘

-- Utils

utest
  cartesian
    (lam e. lam f.
      let arr = tyarrowXe_ tyunknown_ tyunknown_  [] in
      eqType (arr e) (arr f))
    dtcEff dtcEff with
  [ [true,  false]
  , [false, true]
  ] in

let arr_ = lam cs. tyarrowXe_ tyunknown_ tyunknown_ cs _D in

utest
  cartesian
    (lam c. lam d. eqType (arr_ (dtcXDown c)) (arr_ (dtcXDown d))) dtcReg dtcReg
  with
  [ [true,  false, false]
  , [false, true,  false]
  , [false, false, true]
  ] in

-- Subtyping

let arr_ = lam from. lam to. tyarrowXe_ from to [] _D in
utest subtype (arr_ tyunknown_ tyunknown_) (arr_ tyunknown_ tyunknown_) with true in
utest subtype (arr_ tyunknown_ tybot_) (arr_ tyunknown_ tyunknown_) with true in
utest subtype (arr_ tyunknown_ tyunknown_) (arr_ tybot_ tyunknown_) with true in
utest subtype (arr_ tybot_ tyunknown_) (arr_ tyunknown_ tyunknown_) with false in
utest subtype (arr_ tyunknown_ tyunknown_) (arr_ tyunknown_ tybot_) with false in

utest applyBoth joinType (arr_ tyunknown_ tyunknown_) tyunknown_
  with dup (None ())
  using _eqJoin else _toStrJoin in

utest applyBoth joinType (arr_ tyunknown_ tyunknown_) (arr_ tyunknown_ tyunknown_)
  with dup (Some (arr_ tyunknown_ tyunknown_))
  using _eqJoin else _toStrJoin in

utest applyBoth joinType (arr_ tyunknown_ tybot_) (arr_ tyunknown_ tyunknown_)
  with dup (Some (arr_ tyunknown_ tyunknown_))
  using _eqJoin else _toStrJoin in

utest applyBoth joinType (arr_ tybot_ tyunknown_) (arr_ tyunknown_ tyunknown_)
  with dup (Some (arr_ tybot_ tyunknown_))
  using _eqJoin else _toStrJoin in

utest applyBoth meetType (arr_ tyunknown_ tyunknown_) tyunknown_
  with dup tybot_
  using _eqMeet else _toStrMeet in

utest applyBoth meetType (arr_ tyunknown_ tyunknown_) (arr_ tyunknown_ tyunknown_)
  with dup (arr_ tyunknown_ tyunknown_)
  using _eqMeet else _toStrMeet in

utest applyBoth meetType (arr_ tyunknown_ tybot_) (arr_ tyunknown_ tyunknown_)
  with dup (arr_ tyunknown_ tybot_)
  using _eqMeet else _toStrMeet in

utest applyBoth meetType (arr_ tybot_ tyunknown_) (arr_ tyunknown_ tyunknown_)
  with dup (arr_ tyunknown_ tyunknown_)
  using _eqMeet else _toStrMeet in

let arr_ = lam cs. lam e. tyarrowXe_ tyunknown_ tyunknown_ cs e in
utest subtype (arr_ [] _D) (arr_ [] _D) with true in
utest subtype (arr_ [] _D) (arr_ [] _R) with true in
utest subtype (arr_ [] _R) (arr_ [] _D) with false in
utest subtype (arr_ [] _D) (arr_ [] _D) with true in

utest applyBoth joinType (arr_ [] _D) (arr_ [] _D)
  with dup (Some (arr_ [] _D))
  using _eqJoin else _toStrJoin in

utest applyBoth joinType (arr_ [] _R) (arr_ [] _D)
  with dup (Some (arr_ [] _R))
  using _eqJoin else _toStrJoin in

utest applyBoth joinType (arr_ [] _D) (arr_ [] _D)
  with dup (Some (arr_ [] _D))
  using _eqJoin else _toStrJoin in

utest applyBoth joinType (arr_ [] _D) (arr_ [_A] _D)
  with dup (Some (arr_ [_A] _D))
  using _eqJoin else _toStrJoin in

utest applyBoth joinType (arr_ [_C] _D) (arr_ [_A, _P] _D)
  with dup (Some (arr_ [_C, _P,_A] _D))
  using _eqJoin else _toStrJoin in

utest applyBoth meetType (arr_ [] _D) (arr_ [] _D)
  with dup (arr_ [] _D)
  using _eqMeet else _toStrMeet in

utest applyBoth meetType (arr_ [] _R) (arr_ [] _D)
  with dup (arr_ [] _D)
  using _eqMeet else _toStrMeet in

utest applyBoth meetType (arr_ [] _D) (arr_ [] _D)
  with dup (arr_ [] _D)
  using _eqMeet else _toStrMeet in

utest applyBoth meetType (arr_ [_A] _D) (arr_ [_C,_P,_A] _D)
  with dup (arr_ [_A] _D)
  using _eqMeet else _toStrMeet in

utest applyBoth meetType (arr_ [_C] _D) (arr_ [_A, _P] _D)
  with dup (arr_ [] _D)
  using _eqMeet else _toStrMeet in

-- ┌────────────┐
-- │ Test TySeq │
-- └────────────┘

-- Utils

utest eraseDecorationsType (tyseq_ (tyfloatX_ [])) with tyseq_ tyfloat_
  using eqType in

-- Subtyping

utest subtype (tyseq_ tyunknown_) (tyseq_ tyunknown_) with true in
utest applyBoth subtype (tyseq_ tyunknown_) tyunknown_ with dup false in
utest subtype (tyseq_ tybot_) (tyseq_ tyunknown_) with true in
utest subtype (tyseq_ tyunknown_) (tyseq_ tybot_) with false in

utest applyBoth joinType (tyseq_ tyunknown_) (tyseq_ tyunknown_)
  with dup (Some (tyseq_ tyunknown_))
  using _eqJoin else _toStrJoin in

utest applyBoth joinType (tyseq_ tyunknown_) tyunknown_
  with dup (None ())
  using _eqJoin else _toStrJoin in

utest applyBoth joinType (tyseq_ tybot_) (tyseq_ tyunknown_)
  with dup (Some (tyseq_ tyunknown_))
  using _eqJoin else _toStrJoin in

utest applyBoth joinType (tyseq_ (tyseq_ tybot_)) (tyseq_ tyunknown_)
  with dup (None ())
  using _eqJoin else _toStrJoin in

utest applyBoth meetType (tyseq_ tyunknown_) (tyseq_ tyunknown_)
  with dup (tyseq_ tyunknown_)
  using _eqMeet else _toStrMeet in

utest applyBoth meetType (tyseq_ tyunknown_) tyunknown_
  with dup tybot_
  using _eqMeet else _toStrMeet in

utest applyBoth meetType (tyseq_ tybot_) (tyseq_ tyunknown_)
  with dup (tyseq_ tybot_)
  using _eqMeet else _toStrMeet in

utest applyBoth meetType (tyseq_ tyunknown_) tyunknown_
  with dup tybot_
  using _eqMeet else _toStrMeet in

-- ┌───────────────┐
-- │ Test TyRecord │
-- └───────────────┘

-- Utils

utest eraseDecorationsType (tytuple_ [tyunknown_, tyfloatX_ []])
  with tytuple_ [tyunknown_, tyfloat_]
  using eqType in

-- Subtyping

utest applyBoth subtype (tytuple_ []) tyunknown_ with dup false in

utest subtype (tytuple_ [tyunknown_, tybot_]) (tytuple_ [tybot_, tyunknown_])
  with false in

utest
  subtype
    (tytuple_ [tybot_, tybot_])
    (tytuple_ [tybot_, tyunknown_])
  with true in

utest applyBoth joinType (tytuple_ [tyunknown_]) (tytuple_ [tyunknown_])
  with dup (Some (tytuple_ [tyunknown_]))
  using _eqJoin else _toStrJoin in

utest applyBoth joinType (tytuple_ [tyunknown_]) tyunknown_
  with dup (None ())
  using _eqJoin else _toStrJoin in

utest
  applyBoth joinType
    (tytuple_ [tybot_, tybot_])
    (tytuple_ [tybot_, tyunknown_])
  with dup (Some (tytuple_ [tybot_, tyunknown_]))
  using _eqJoin else _toStrJoin in

utest applyBoth meetType (tytuple_ [tyunknown_]) (tytuple_ [tyunknown_])
  with dup (tytuple_ [tyunknown_])
  using _eqMeet else _toStrMeet in

utest applyBoth meetType (tytuple_ [tyunknown_]) tyunknown_
  with dup tybot_
  using _eqMeet else _toStrMeet in

utest
  applyBoth meetType
    (tytuple_ [tybot_, tybot_])
    (tytuple_ [tybot_, tyunknown_])
  with dup (tytuple_ [tybot_, tybot_])
  using _eqMeet else _toStrMeet in

-- ┌────────────┐
-- │ TEST TERMS │
-- └────────────┘

let _typeOf = lam env. lam tm. (result.consume (typeOf (dtcEnvOfSeq env) tm)).1 in

let eq =
  -- Either compare the type or the error constructors
  eitherEq
    (lam l. lam r.
      forAll (lam x. x)
        (zipWith (lam l. lam r. eqi (constructorTag l) (constructorTag r)) l r))
    (tupleEq2 dtcEqe eqType) in

let toString =
  eitherEither
    (lam errs. strJoin "\n" (map typeErrorToString errs))
    (lam t. join [":", dtcEffectToString t.0, " ", type2str t.1])
in
let onFail = utestDefaultToString toString toString in

-- Shorthand types
let arrce = lam ps. lam ret. foldr (lam t. lam to. tyarrowXe_ t.0 to t.1 t.2) ret ps in
let arrc = lam ps. arrce (map (lam p. (p.0, p.1, _D)) ps) in
let arre = lam ps. arrce (map (lam p. (p.0, [], p.1)) ps) in
let arr = lam ps. arrce (map (lam p. (p, [], _D)) ps) in
let flt = tyfloatc_ in
let fltX = tyfloatX_ in

-- Shorthand names
let _x = nameNoSym "x" in
let _y = nameNoSym "y" in
let _z = nameNoSym "z" in
let _u = nameNoSym "u" in
let _v = nameNoSym "v" in
let _w = nameNoSym "w" in
let _f = nameNoSym "f" in
let _g = nameNoSym "g" in
let _h = nameNoSym "h" in

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

-- ┌──────────────────────┐
-- │ Test Lambda Calculus │
-- └──────────────────────┘

utest _typeOf [] (lam_ [(_x, flt _A)] x)
  with Right (_D, arrc [(flt _A, [])] (flt _A))
  using eq else onFail in

utest _typeOf [] (lam_ [(_x, flt _P)] x)
  with Right (_D, arrc [(flt _P, [])] (flt _P))
  using eq else onFail in

utest _typeOf [] (lam_ [(_x, fltX dtcPC)] x)
  with Right (_D, arrc [(fltX dtcPC, [])] (fltX dtcPC))
  using eq else onFail in

utest
  _typeOf
    [ (_f, arrc [(flt _A, [_P, _A])] (flt _A))
    , (_x, flt _P)
    ]
    (f [x])
  with Right (_D, flt _A)
  using eq else onFail in

utest
  _typeOf
    [ (_f, arrc [(flt _A, [_P])] (flt _A))
    , (_x, flt _P)
    ]
    (f [x])
  with Right (_D, flt _P)
  using eq else onFail in

utest
  _typeOf
    [ (_f, arrc [(flt _A, [_P])] (flt _A))
    , (_x, fltX [])
    ]
    (f [x])
  with Right (_D, flt _P)
  using eq else onFail in

utest
  _typeOf
    [ (_f, arrc [(fltX dtcPC, [])] (flt _A))
    , (_x, flt _P)
    ]
    (f [x])
  with Right (_D, flt _P)
  using eq else onFail in

utest
  _typeOf
    [ (_f, arrc [(fltX dtcPC, [])] (flt _A))
    , (_x, flt _C)
    ]
    (f [x])
  with Right (_D, flt _C)
  using eq else onFail in

utest
  _typeOf
    [ (_f, arrc [(fltX dtcPC, [])] (flt _A))
    , (_x, fltX dtcPC)
    ]
    (f [x])
  with Right (_D, fltX dtcPC)
  using eq else onFail in

utest
  _typeOf
    [ (_f, arrc [(flt _P, [])] (flt _A))
    , (_x, flt _A)
    ]
    (f [x])
  with Left [DTCArgError (NoInfo (), (None ()))]
  using eq else onFail in

utest
  _typeOf
    [ (_f, arrc [(arrc [(flt _P, [_P])] (flt _A), [_P])] (flt _A))
    , (_x, arrc [(flt _A, [_P])] (flt _P))
    ]
    (f [x])
  with Right (_D, flt _P)
  using eq else onFail in

utest
  _typeOf
    [ (_f, arrc [(arrc [(flt _P, [_P])] (flt _A), [_P])] (flt _A))
    , (_x, arrc [(flt _A, [])] (flt _P))
    ]
    (f [x])
  with Right (_D, flt _P)
  using eq else onFail in

utest
  _typeOf
    [ (_f, arrc [(arrc [(flt _P, [_P])] (flt _A), [_A])] (flt _A))
    , (_x, arrc [(flt _A, [])] (flt _P))
    ]
    (f [x])
  with Right (_D, flt _A)
  using eq else onFail in

utest
  _typeOf
    [ (_f, arrc [(arrc [(flt _P, [_P])] (flt _A), [_A])] (flt _A))
    , (_x, arrc [(flt _A, [_C])] (flt _P))
    ]
    (f [x])
  with Left [DTCArgError (NoInfo (), (None ()))]
  using eq else onFail in

utest
  _typeOf
    [ (_f, arrc [(arrc [(flt _P, [_P])] (flt _P), [_A])] (flt _A))
    , (_x, arrc [(flt _A, [])] (flt _A))
    ]
    (f [x])
  with Left [DTCArgError (NoInfo (), (None ()))]
  using eq else onFail in

utest
  _typeOf
    [ (_f, arrc [(arrc [(flt _P, [_P])] (flt _A), [_A])] (flt _A))
    , (_x, arrc [(fltX [], [])] (flt _P))
    ]
    (f [x])
  with Left [DTCArgError (NoInfo (), (None ()))]
  using eq else onFail in

-- Should invoke lowercover check
utest
  _typeOf
    [ ( _f
      , arrc
          [(arrc [(flt _A, [_A,_P,_C])] (flt _A), [])]
          (arrc [(flt _A, [_A])] (flt _A))
      )
    , (_x, arrc [(flt _A, [_P])] (flt _A))
    ]
    (f [x])
  with Right (_D, arrc [(flt _A, [_A])] (flt _A))
  using eq else onFail in

-- Should invoke lowercover check
utest
  _typeOf
    [ ( _f
      , arrc
          [(arrc [(flt _A, [_A,_P,_C])] (flt _A), [])]
          (arrc [(flt _A, [_A, _P])] (flt _A))
      )
    , (_x, arrc [(flt _A, [_C])] (flt _A))
    ]
    (f [x])
  with Right (_D, arrc [(flt _A, [_A])] (flt _A))
  using eq else onFail in

-- Should invoke lowercover check
utest
  _typeOf
    [ ( _f
      , arrc
          [(arrc [(flt _A, [_A,_P,_C])] (flt _A), [])]
          (arrc [(flt _A, [_P])] (flt _A))
      )
    , (_x, arrc [(flt _A, [_C])] (flt _A))
    ]
    (f [x])
  with Right (_D, arrc [(flt _A, [])] (flt _A))
  using eq else onFail in

-- ┌─────────────┐
-- │ Test Tuples │
-- └─────────────┘

utest
  _typeOf
    [(_x, tytuple_ [flt _P, flt _C])]
    (utuple_ [tupleproj_ 1 x, tupleproj_ 0 x])
  with Right (_D, tytuple_ [flt _C, flt _P])
  using eq else onFail in

-- ┌──────────┐
-- │ Test Seq │
-- └──────────┘

utest
  _typeOf
    [ (_x, tyseq_ (flt _P))
    , (_y, tyint_)
    , (_z, flt _C)
    ]
    (set_ x y z)
  with Right (_D, tyseq_ (fltX dtcPC))
  using eq else onFail in
utest
  _typeOf
    [ (_x, tyint_)
    , (_y, tyint_)
    , (_z, flt _C)
    ]
    (set_ x y z)
  with Left [DTCPolyConstError (NoInfo ())]
  using eq else onFail in

utest
  _typeOf
    [ (_x, tyseq_ (flt _A))
    , (_y, tyint_)
    ]
    (get_ x y)
  with Right (_D, flt _A)
  using eq else onFail in
utest
  _typeOf
    [ (_x, tyint_)
    , (_y, tyint_)
    ]
    (get_ x y)
  with Left [DTCPolyConstError (NoInfo ())]
  using eq else onFail in

utest
  _typeOf
    [ (_x, flt _P)
    , (_y, tyseq_ (flt _C))
    ]
    (cons_ x y)
  with Right (_D, tyseq_ (fltX dtcPC))
  using eq else onFail in
utest
  _typeOf
    [ (_x, flt _P)
    , (_y, tyint_)
    ]
    (cons_ x y)
  with Left [DTCPolyConstError (NoInfo ())]
  using eq else onFail in

utest
  _typeOf
    [ (_x, tyseq_ (flt _P))
    , (_y, flt _C)
    ]
    (snoc_ x y)
  with Right (_D, tyseq_ (fltX dtcPC))
  using eq else onFail in
utest
  _typeOf
    [ (_x, tyint_)
    , (_y, flt _C)
    ]
    (snoc_ x y)
  with Left [DTCPolyConstError (NoInfo ())]
  using eq else onFail in

utest
  _typeOf
    [ (_x, tyseq_ (flt _P))
    , (_y, tyseq_ (flt _C))
    ]
    (concat_ x y)
  with Right (_D, tyseq_ (fltX dtcPC))
  using eq else onFail in
utest
  _typeOf
    [ (_x, tyint_)
    , (_y, tyseq_ (flt _C))
    ]
    (concat_ x y)
  with Left [DTCPolyConstError (NoInfo ())]
  using eq else onFail in

utest _typeOf [(_x, tyseq_ (flt _A))] (length_ x) with Right (_D, tyint_)
  using eq else onFail in
utest _typeOf [(_x, tyint_)] (length_ x)
  with Left [DTCPolyConstError (NoInfo ())]
  using eq else onFail in

utest _typeOf [(_x, tyseq_ (flt _A))] (reverse_ x)
  with Right (_D, tyseq_ (flt _A))
  using eq else onFail in
utest _typeOf [(_x, tyint_)] (reverse_ x)
  with Left [DTCPolyConstError (NoInfo ())]
  using eq else onFail in

utest _typeOf [(_x, tyseq_ (flt _A))] (head_ x) with Right (_D, flt _A)
  using eq else onFail in
utest _typeOf [(_x, tyint_)] (head_ x)
  with Left [DTCPolyConstError (NoInfo ())]
  using eq else onFail in

utest _typeOf [(_x, tyseq_ (flt _A))] (tail_ x) with Right (_D, tyseq_ (flt _A))
  using eq else onFail in
utest _typeOf [(_x, tyint_)] (tail_ x)
  with Left [DTCPolyConstError (NoInfo ())]
  using eq else onFail in

let _test = lam c.
  _typeOf [
    (_x, tyseq_ (flt _A))
  ] (app_ (uconst_ c) x)
in

let onFailConst = lam c. lam x. lam y.
  concat
    (join ["Const: ", getConstStringCode 0 c, "\n"])
    (onFail x y) in

iter
  (lam c.
    utest _test c with Right (_D, tybool_) using eq else onFailConst c in
    utest
      _typeOf [(_x, tyint_)] (app_ (uconst_ c) x)
      with Left [DTCPolyConstError (NoInfo ())]
      using eq else onFailConst c in
    ())
  [CNull (), CIsList (), CIsRope ()];

let _test = lam e.
  _typeOf
    [ (_x, arre [(flt _A, e)] (flt _C))
    , (_y, tyseq_ (flt _P))
    ]
    (map_ x y) in

let _expected = lam e. Right (e, tyseq_ (fltX [])) in

utest _test _D with _expected _D using eq else onFail in
utest _test _R with _expected _R using eq else onFail in
utest
  _typeOf
    [ (_x, arre [(flt _A, _D)] (flt _C))
    , (_y, tyint_)
    ]
    (map_ x y)
  with Left [DTCPolyConstError (NoInfo ())]
  using eq else onFail in

let _test = lam e1. lam e2.
  _typeOf
    [ (_x, arre [(tyint_, e1), (flt _A, e2)] (flt _C))
    , (_y, tyseq_ (flt _P))
    ]
    (mapi_ x y) in

let _expected = lam e. Right (e, tyseq_ (fltX [])) in

utest _test _D _D with _expected _D using eq else onFail in
utest _test _R _D with _expected _R using eq else onFail in
utest _test _D _R with _expected _R using eq else onFail in
utest _test _R _R with _expected _R using eq else onFail in
utest
  _typeOf
    [ (_x, arr [(flt _A), (flt _A)] (flt _C))
    , (_y, tyseq_ (flt _P))
    ]
    (mapi_ x y)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail in
utest
  _typeOf
    [ (_x, arr [tyint_, tyint_] (flt _C))
    , (_y, tyseq_ (flt _P))
    ]
    (mapi_ x y)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail in
utest
  _typeOf
    [ (_x, arre [(tyint_, _D), (flt _A, _D)] (flt _C))
    , (_y, tyint_)
    ]
    (mapi_ x y)
  with Left [DTCPolyConstError (NoInfo ())]
  using eq else onFail in

let _test = lam e.
  _typeOf
    [ (_x, arre [(flt _A, e)] tyunit_)
    , (_y, tyseq_ (flt _P))
    ]
    (iter_ x y) in

let _expected = lam e. Right (e, tyunit_) in

utest _test _D with _expected _D using eq else onFail in
utest _test _R with _expected _R using eq else onFail in
utest
  _typeOf
    [ (_x, arr [flt _A] tyint_)
    , (_y, tyseq_ (flt _P))
    ]
    (iter_ x y)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail in
utest
  _typeOf
    [ (_x, arr [tyint_] tyunit_)
    , (_y, tyseq_ (flt _P))
    ]
    (iter_ x y)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail in
utest
  _typeOf
    [ (_x, arre [(flt _A, _D)] tyunit_)
    , (_y, tyint_)
    ]
    (iter_ x y)
  with Left [DTCPolyConstError (NoInfo ())]
  using eq else onFail in

let _test = lam e1. lam e2.
  _typeOf
    [ (_x, arre [(tyint_, e1), (flt _A, e2)] tyunit_)
    , (_y, tyseq_ (flt _P))
    ]
    (iteri_ x y) in

let _expected = lam e. Right (e, tyunit_) in

utest _test _D _D with _expected _D using eq else onFail in
utest _test _R _D with _expected _R using eq else onFail in
utest _test _D _R with _expected _R using eq else onFail in
utest _test _R _R with _expected _R using eq else onFail in
utest
  _typeOf
    [ (_x, arr [(flt _A), (flt _A)] tyunit_)
    , (_y, tyseq_ (flt _P))
    ]
    (iteri_ x y)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail in
utest
  _typeOf
    [ (_x, arr [tyint_, tyint_] tyunit_)
    , (_y, tyseq_ (flt _P))
    ]
    (iteri_ x y)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail in
utest
  _typeOf
    [ (_x, arre [(tyint_, _D), (flt _A, _D)] tyunit_)
    , (_y, tyint_)
    ]
    (iteri_ x y)
  with Left [DTCPolyConstError (NoInfo ())]
  using eq else onFail in

let _test = lam e1. lam e2.
  _typeOf
    [ (_x, arre [(flt _C, e1), (flt _A, e2)] (flt _C))
    , (_y, fltX [])
    , (_z, tyseq_ (flt _P))
    ]
    (foldl_ x y z) in

let _expected = lam e. Right (e, fltX []) in

utest _test _D _D with _expected _D using eq else onFail in
utest _test _R _D with _expected _R using eq else onFail in
utest _test _D _R with _expected _R using eq else onFail in
utest _test _R _R with _expected _R using eq else onFail in
utest
  _typeOf
    [ (_x, arr [tyint_, flt _A] (flt _C))
    , (_y, fltX [])
    , (_z, tyseq_ (flt _P))
    ]
    (foldl_ x y z)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail in
utest
  _typeOf
    [ (_x, arr [flt _C, tyint_] (flt _C))
    , (_y, fltX [])
    , (_z, tyseq_ (flt _P))
    ]
    (foldl_ x y z)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail in
utest
  _typeOf
    [ (_x, arre [(flt _C, _D), (flt _A, _D)] (flt _C))
    , (_y, fltX [])
    , (_z, tyint_)
    ]
    (foldl_ x y z)
  with Left [DTCPolyConstError (NoInfo ())]
  using eq else onFail in

let _test = lam e1. lam e2.
  _typeOf
    [ (_x, arre [(flt _A, e1), (flt _C, e2)] (flt _C))
    , (_y, fltX [])
    , (_z, tyseq_ (flt _P))
    ]
    (foldr_ x y z) in

let _expected = lam e. Right (e, fltX []) in

utest _test _D _D with _expected _D using eq else onFail in
utest _test _R _D with _expected _R using eq else onFail in
utest _test _D _R with _expected _R using eq else onFail in
utest _test _R _R with _expected _R using eq else onFail in
utest
  _typeOf
    [ (_x, arr [flt _A, tyint_] (flt _C))
    , (_y, fltX [])
    , (_z, tyseq_ (flt _P))
    ]
    (foldr_ x y z)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail in
utest
  _typeOf
    [ (_x, arr [flt _A, flt _C] tyint_)
    , (_y, fltX [])
    , (_z, tyseq_ (flt _P))
    ]
    (foldr_ x y z)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail in
utest
  _typeOf
    [ (_x, arr [tyint_, flt _C] (flt _C))
    , (_y, fltX [])
    , (_z, tyseq_ (flt _P))
    ]
    (foldr_ x y z)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail in
utest
  _typeOf
    [ (_x, arre [(flt _A, _D), (flt _C, _D)] (flt _C))
    , (_y, fltX [])
    , (_z, tyint_)
    ]
    (foldr_ x y z)
  with Left [DTCPolyConstError (NoInfo ())]
  using eq else onFail in

iter
  (lam c.
    let _test = lam e.
      _typeOf [
        (_x, tyint_),
        (_y, arre [(tyint_, e)] (flt _A))
     ] (appf2_ (uconst_ c) x y)
    in
    let _expected = lam e. Right (e, tyseq_ (fltX [])) in
    utest _test _D with _expected _D using eq else onFail in
    utest _test _R with _expected _R using eq else onFail in
    utest
      _typeOf [
        (_x, tyint_),
        (_y, arr [flt _A] (flt _A))
      ] (appf2_ (uconst_ c) x y)
      with Left [DTCArgError (NoInfo (), None ())]
      using eq else onFail in
    ())
  [CCreate (), CCreateList (), CCreateRope ()];

utest
  _typeOf
    [ (_x, tyseq_ (flt _A))
    , (_y, tyint_)
    ]
    (splitat_ x y)
  with Right (_D, tytuple_ [tyseq_ (flt _A), tyseq_ (flt _A)])
  using eq else onFail in
utest
  _typeOf
    [ (_x, tyseq_ (flt _A))
    , (_y, flt _A)
    ]
    (splitat_ x y)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail in
utest
  _typeOf
    [ (_x, tyint_)
    , (_y, tyint_)
    ]
    (splitat_ x y)
  with Left [DTCPolyConstError (NoInfo ())]
  using eq else onFail in

utest
  _typeOf
    [ (_x, tyseq_ (flt _A))
    , (_y, tyint_)
    , (_z, tyint_)
    ]
    (subsequence_ x y z)
  with Right (_D, tyseq_ (flt _A))
  using eq else onFail in
utest
  _typeOf
    [ (_x, tyseq_ (flt _A))
    , (_y, flt _A)
    , (_z, tyint_)
    ]
    (subsequence_ x y z)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail in
utest
  _typeOf
    [ (_x, tyseq_ (flt _A))
    , (_y, tyint_)
    , (_z, flt _A)
    ]
    (subsequence_ x y z)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail in
utest
  _typeOf
    [ (_x, tyint_)
    , (_y, tyint_)
    , (_z, tyint_)
    ]
    (subsequence_ x y z)
  with Left [DTCPolyConstError (NoInfo ())]
  using eq else onFail in

-- ┌─────────────────┐
-- │ Test Intrinsics │
-- └─────────────────┘

utest _typeOf [] (float_ 0.) with Right (_D, fltX [])
  using eq else onFail in

utest _typeOf [] (int_ 0) with Right (_D, tyint_)
  using eq else onFail in

iter
  (lam c.
    utest
      _typeOf
        [ (_x, flt _A)
        , (_y, flt _A)
        ]
        (appf2_ (uconst_ c) x y)
      with Right (_D, flt _A)
      using eq else onFailConst c in

    utest
      _typeOf
        [ (_x, flt _A)
        , (_y, fltX [])
        ]
        (appf2_ (uconst_ c) x y)
      with Right (_D, flt _A)
      using eq else onFailConst c in

    utest
      _typeOf
        [ (_x, flt _P)
        , (_y, flt _C)
        ]
        (appf2_ (uconst_ c) x y)
      with Right (_D, fltX dtcPC)
      using eq else onFailConst c in

    ())
  [CAddf (), CSubf (), CMulf (), CPow ()];

utest
  _typeOf
    [ (_x, flt _A)
    , (_y, flt _P)
    ]
    (divf_ x y)
  with Right (_D, flt _A)
  using eq else onFail in

utest
  _typeOf
    [ (_x, flt _C)
    , (_y, flt _P)
    ]
    (divf_ x y)
  with Right (_D, fltX dtcPC)
  using eq else onFail in

utest
  _typeOf
    [ (_x, flt _A)
    , (_y, flt _A)
    ]
    (divf_ x y)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail in

utest
  _typeOf
    [ (_x, flt _A)
    , (_y, flt _C)
    ]
    (divf_ x y)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail in

iter
  (lam c.
    utest
      _typeOf
        [ (_x, flt _A)
        ]
        (appf2_ (uconst_ c) (int_ 0) x)
      with Left [DTCArgError (NoInfo (), None ())]
      using eq else onFailConst c in

    utest
      _typeOf
        [ (_x, flt _A)
        ]
        (appf2_ (uconst_ c) x (int_ 0))
      with Left [DTCArgError (NoInfo (), None ())]
      using eq else onFailConst c in

    utest
      _typeOf
        [ (_x, flt _A)
        ]
        (appf1_ (uconst_ c) x)
      with Left [DTCPartiallyAppliedConst (NoInfo (), None ())]
      using eq else onFailConst c in

    ())
  [ CAddf ()
  , CSubf ()
  , CMulf ()
  , CDivf ()
  , CPow ()
  , CEqf ()
  , CLtf ()
  , CLeqf ()
  , CGtf ()
  , CGeqf ()
  , CNeqf ()
  ];

iter
  (lam c.
    utest
      _typeOf [ (_x, flt _A)] (appf1_ (uconst_ c) x)
      with Right (_D, flt _A)
      using eq else onFailConst c in

    utest _typeOf [ (_x, flt _P)] (appf1_ (uconst_ c) x)
      with Right (_D, flt _P)
      using eq else onFailConst c in

    ())
  [CNegf (), CSin (), CCos (), CExp ()];

iter
  (lam c.
    utest
      _typeOf [ (_x, flt _A)] (appf1_ (uconst_ c) x)
      with Left [DTCArgError (NoInfo (), None ())]
      using eq else onFailConst c in

    utest _typeOf [ (_x, flt _P)] (appf1_ (uconst_ c) x)
      with Right (_D, flt _P)
      using eq else onFailConst c in

    utest _typeOf [ (_x, flt _C)] (appf1_ (uconst_ c) x)
      with Left [DTCArgError (NoInfo (), None ())]
      using eq else onFailConst c in

    utest _typeOf [ (_x, fltX [])] (appf1_ (uconst_ c) x)
      with Right (_D, fltX [])
      using eq else onFailConst c in

    ())
  [CLog (), CSqrt ()];

utest
  _typeOf [ (_x, flt _A)] (absf_ x)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail in

utest
  _typeOf [ (_x, flt _P)] (absf_ x)
  with Right (_D, flt _P)
  using eq else onFail in

utest
  _typeOf [ (_x, flt _C)] (absf_ x)
  with Right (_D, flt _C)
  using eq else onFail in

utest
  _typeOf [ (_x, fltX dtcPC)] (absf_ x)
  with Right (_D, fltX dtcPC)
  using eq else onFail in

utest
  _typeOf [ (_x, flt _C)] (absf_ x)
  with Right (_D, flt _C)
  using eq else onFail in

iter
  (lam c.
    utest
      _typeOf [] (appf1_ (uconst_ c) (int_ 0))
      with Left [DTCArgError (NoInfo (), None ())]
      using eq else onFailConst c in

    utest _typeOf [] (uconst_ c)
      with Left [DTCPartiallyAppliedConst (NoInfo (), None ())]
      using eq else onFailConst c in

    ())
  [CNegf (), CSin (), CCos (), CExp (), CLog (), CSqrt (), CAbsf ()];

-- ┌───────────┐
-- │ Test Diff │
-- └───────────┘

utest
  _typeOf
    [ (_x, arrc [(flt _A, [_A,_P])] (flt _A))
    , (_y, flt _A)
    , (_z, flt _A)
    ]
    (diff_ x y z)
  with Right (_D, flt _A)
  using eq else onFail in

utest
  _typeOf
    [ (_x, arrc [(flt _A, [_P])] (flt _A))
    , (_y, flt _P)
    , (_z, flt _P)
    ]
    (diff_ x y z)
  with Right (_D, flt _P)
  using eq else onFail in

utest
  _typeOf
    [ (_x, arrc [(flt _A, [])] (flt _A))
    , (_y, fltX [])
    , (_z, fltX [])
    ]
    (diff_ x y z)
  with Right (_D, fltX [])
  using eq else onFail in

utest
  _typeOf
    [ (_x, arrc [(flt _A, [_A,_P])] (flt _C))
    , (_y, flt _A)
    , (_z, flt _A)
    ]
    (diff_ x y z)
  with Right (_D, flt _A)
  using eq else onFail in

utest
  _typeOf
    [ (_x, arrc [(flt _P, [_P])] (flt _P))
    , (_y, flt _P)
    , (_z, flt _P)
    ]
    (diff_ x y z)
  with Right (_D, flt _P)
  using eq else onFail in

utest
  _typeOf
    [ (_x, arrc [(flt _P, [])] (fltX []))
    , (_y, fltX [])
    , (_z, fltX [])
    ]
    (diff_ x y z)
  with Right (_D, fltX [])
  using eq else onFail in

utest
  _typeOf
    [ (_x, arrc [(tytuple_ [flt _A, flt _A], [_A,_P])] (tytuple_ [flt _A]))
    , (_y, tytuple_ [flt _A, flt _A])
    , (_z, tytuple_ [flt _A, flt _A])
    ]
    (diff_ x y z)
  with Right (_D, tytuple_ [flt _A])
  using eq else onFail in

utest
  _typeOf
    [ (_x, arrc [(tyseq_ (flt _A), [_A, _P])] (tyseq_ (flt _A)))
    , (_y, tyseq_ (flt _A))
    , (_z, tyseq_ (flt _A))
    ]
    (diff_ x y z)
  with Right (_D, tyseq_ (flt _A))
  using eq else onFail in

utest
  _typeOf
    [ (_x, arrc [(tytuple_ [flt _A], [_A,_P])] (tytuple_ [flt _A]))
    , (_y, tytuple_ [flt _A, flt _A])
    , (_z, tytuple_ [flt _A])
    ]
    (diff_ x y z)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail in

utest
  _typeOf
    [ (_x, arrc [(tytuple_ [flt _A], [_A,_P])] (tytuple_ [flt _A]))
    , (_y, tytuple_ [flt _A])
    , (_z, tytuple_ [flt _A, flt _A])
    ]
    (diff_ x y z)
  with Left [DTCArgError (NoInfo (), None ())]
  using eq else onFail in

utest
  _typeOf
    [ (_x, arrc [(tyint_, [_A,_P])] (flt _A))
    , (_y, flt _A)
    , (_z, flt _A)
    ]
    (diff_ x y z)
  with Left [DTCDiffFnNotRnError (NoInfo (), None ())]
  using eq else onFail in

utest
  _typeOf
    [ (_x, arrc [(flt _A, [_A,_P])] tyint_)
    , (_y, flt _A)
    , (_z, flt _A)
    ]
    (diff_ x y z)
  with Left [DTCDiffFnNotRnError (NoInfo (), None ())]
  using eq else onFail in

utest
  _typeOf
    [ (_x, arrc [(flt _C, [_A,_P])] (flt _A))
    , (_y, flt _C)
    , (_z, flt _C)
    ]
    (diff_ x y z)
  with Left [DTCDiffFnError (NoInfo (), None ())]
  using eq else onFail in

utest
  _typeOf
    [ (_x, arrc [(flt _P, [_C])] (flt _P))
    , (_y, flt _P)
    , (_z, flt _P)
    ]
    (diff_ x y z)
  with Left [DTCDiffFnError (NoInfo (), None ())]
  using eq else onFail in

utest
  _typeOf
    [ (_x, arrc [(flt _P, [_A])] (flt _P))
    , (_y, flt _P)
    , (_z, flt _P)
    ]
    (diff_ x y z)
  with Left [DTCDiffFnError (NoInfo (), None ())]
  using eq else onFail in

utest
  _typeOf
    [ (_x, arrce [(flt _A, [_A,_P], _R)] (flt _A))
    , (_y, flt _A)
    , (_z, flt _A)
    ]
    (diff_ x y z)
  with Left [DTCDiffFnError (NoInfo (), None ())]
  using eq else onFail in

-- ┌───────────────────────────┐
-- │ Test eraseDecorationsType │
-- └───────────────────────────┘

-- utest eraseDecorationsType (tyfloatc_ _A) with tyfloat_ using eqType in
-- utest
--   eraseDecorationsType
--     (tyarrowce_
--        (tyfloatc_ _A)
--        (tyarrowce_ (tychar_) (tyfloatc_ _A) _A _D)
--       _A _D)
--   with tyarrow_ tyfloat_ (tyarrow_ tychar_ tyfloat_) using eqType
-- in

-- -- ┌───────────────┐
-- -- │ Test leqcType │
-- -- └───────────────┘
--
-- utest leqcType _A (tyfloatc_ _A) with true in
-- utest leqcType _A (tyfloatc_ _P) with false in
-- utest leqcType _P (tyfloatc_ _A) with true in
-- let rhs = tytuple_ [
--   tyfloatc_ _P,
--   tyseq_ (tyfloatc_ _M),
--   tytuple_ [tyfloatc_ _C],
--   tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _A _D
-- ] in
-- utest leqcType _A rhs with false in
-- utest leqcType _PC rhs with false in
-- utest leqcType _P rhs with false in
-- utest leqcType _C rhs with false in
-- utest leqcType _M rhs with true in
--
-- -- ┌──────────────┐
-- -- │ Test eqcType │
-- -- └──────────────┘
--
-- utest eqcType _A (tyfloatc_ _A) with true in
-- utest eqcType _A (tyfloatc_ _P) with false in
-- utest eqcType _P (tyfloatc_ _A) with false in
-- let rhs = tytuple_ [
--   tyfloatc_ _P,
--   tytuple_ [tyfloatc_ _C],
--   tyseq_ (tyfloatc_ _M),
--   tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _A _D
-- ] in
-- utest eqcType _A rhs with false in
-- utest eqcType _PC rhs with false in
-- utest eqcType _P rhs with false in
-- utest eqcType _C rhs with false in
-- utest eqcType _M rhs with false in
-- let rhs = lam c. tytuple_ [
--   tyfloatc_ c,
--   tyseq_ (tyfloatc_ c)
-- ] in
-- utest eqcType _A (rhs _A) with true in
-- utest eqcType _P (rhs _A) with false in
-- utest eqcType _PC (rhs _PC) with true in
-- utest eqcType _C (rhs _A) with false in
-- utest eqcType _M (rhs _A) with false in
-- utest eqcType _A (rhs _P) with false in
-- utest eqcType _P (rhs _P) with true in
-- utest eqcType _C (rhs _P) with false in
-- utest eqcType _M (rhs _P) with false in
-- let rhs = tytuple_ [
--   tyfloatc_ _M,
--   tyseq_ (tyfloatc_ _M),
--   tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _M _D
-- ] in
-- utest eqcType _A rhs with false in
-- utest eqcType _PC rhs with false in
-- utest eqcType _P rhs with false in
-- utest eqcType _C rhs with false in
-- utest eqcType _M rhs with true in
--
-- -- ┌───────────────┐
-- -- │ Test leqTypec │
-- -- └───────────────┘
--
-- utest leqTypec (tyfloatc_ _A) _A with true in
-- utest leqTypec (tyfloatc_ _P) _A with true in
-- utest leqTypec (tyfloatc_ _A) _P with false in
-- let rhs = tytuple_ [
--   tyfloatc_ _P,
--   tytuple_ [tyfloatc_ _C],
--   tyseq_ (tyfloatc_ _M),
--   tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _P _D
-- ] in
-- utest leqTypec rhs _A with true in
-- utest leqTypec rhs _PC with true in
-- utest leqTypec rhs _P with false in
-- utest leqTypec rhs _C with false in
-- utest leqTypec rhs _M with false in
--
-- -- ┌─────────────────┐
-- -- │ Test dtcLeqcEnv │
-- -- └─────────────────┘
--
-- utest dtcLeqcEnv _A (dtcEnvOfSeq []) with true in
-- utest dtcLeqcEnv _A (dtcEnvOfSeq [(_x, tyfloatc_ _A)]) with true in
-- let env = dtcEnvOfSeq [(_x, tyfloatc_ _P), (_y, tyfloatc_ _M)] in
-- utest dtcLeqcEnv _A env with false in
-- utest dtcLeqcEnv _PC env with false in
-- utest dtcLeqcEnv _P env with false in
-- utest dtcLeqcEnv _M env with true in
-- utest
--   dtcLeqcEnv _M
--     (dtcEnvOfSeq [(_x, (tyarrowce_ (tychar_) (tyfloatc_ _A) _A _D))])
--   with true
-- in
--
-- -- ┌───────────────┐
-- -- │ Test mulcType │
-- -- └───────────────┘
--
-- utest mulcType _A (tyfloatc_ _A) with tyfloatc_ _A using eqType in
-- utest mulcType _A (tyfloatc_ _P) with tyfloatc_ _P using eqType in
-- utest mulcType _P (tyfloatc_ _A) with tyfloatc_ _P using eqType in
-- utest mulcType _C (tyfloatc_ _P) with tyfloatc_ _M using eqType in
-- utest mulcType _P (tyfloatc_ _C) with tyfloatc_ _M using eqType in
-- utest mulcType _M (tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _A _D) with
--   tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _M _D using eqType
-- in
-- utest mulcType _P (tytuple_ [tyfloatc_ _A, tyfloatc_ _M]) with
--   tytuple_ [tyfloatc_ _P, tyfloatc_ _M] using eqType
-- in
-- utest mulcType _P (tyseq_ (tyfloatc_ _A))
--   with (tyseq_ (tyfloatc_ _P)) using eqType
-- in
-- utest mulcType _P (tydist_ (tyfloatc_ _A))
--   with (tydist_ (tyfloatc_ _A)) using eqType
-- in
--
-- -- ┌──────────────┐
-- -- │ Test subtype │
-- -- └──────────────┘
--
-- -- Bottom type
-- utest
--   forAll (lam ty. and (subtype (tybot_, ty)) (not (subtype (ty, tybot_))))
--     alltypes
--   with true
-- in
--
-- -- Float
-- let _subtype = lam c1. lam c2.
--   subtype (tyfloatc_ c1, tyfloatc_ c2)
-- in
--
-- utest _subtype _A _A with true in
-- utest _subtype _A _PC with false in
-- utest _subtype _A _P with false in
-- utest _subtype _A _C with false in
-- utest _subtype _A _M with false in
--
-- utest _subtype _PC _A with true in
-- utest _subtype _PC _PC with true in
-- utest _subtype _PC _P with false in
-- utest _subtype _PC _C with false in
-- utest _subtype _PC _M with false in
--
-- utest _subtype _P _A with true in
-- utest _subtype _P _PC with true in
-- utest _subtype _P _P with true in
-- utest _subtype _P _C with false in
-- utest _subtype _P _M with false in
--
-- utest _subtype _C _A with true in
-- utest _subtype _C _PC with true in
-- utest _subtype _C _P with false in
-- utest _subtype _C _C with true in
-- utest _subtype _C _M with false in
--
-- utest _subtype _M _A with true in
-- utest _subtype _M _PC with true in
-- utest _subtype _M _P with true in
-- utest _subtype _M _C with true in
-- utest _subtype _M _M with true in
--
-- utest subtype (tyfloatc_ _A, tytuple_ [tyfloatc_ _A]) with false in
--
-- -- Sequences
-- utest subtype (tyseq_ (tyfloatc_ _P), tyseq_ (tyfloatc_ _A)) with true in
--
-- -- Records
-- let tup2 = lam c1. lam c2. tytuple_ [tyfloatc_ c1, tyfloatc_ c2] in
-- let tup3 = lam c1. lam c2. lam c3.
--   tytuple_ [tyfloatc_ c1, tyfloatc_ c2, tyfloatc_ c2]
-- in
--
-- utest subtype (tup2 _A _A, tup2 _A _A) with true in
-- utest subtype (tup2 _A _A, tup3 _A _A _A) with false in
-- utest subtype (tup3 _A _A _A, tup2 _A _A) with false in
-- utest subtype (tup2 _P _M, tup2 _A _P) with true in
-- utest subtype (tup2 _A _A, tup2 _A _P) with false in
--
-- -- Arrows
-- let arr = lam c1. lam c2. lam e.
--   tyarrowce_ (tyfloatc_ c1) (tyfloatc_ c2) _A e
-- in
--
-- utest subtype (arr _A _A _D, arr _A _A _D) with true in
-- utest subtype (arr _A _A _D, arr _A _A _R) with true in
-- utest subtype (arr _A _A _R, arr _A _A _R) with true in
-- utest subtype (arr _A _A _R, arr _A _A _D) with false in
-- utest subtype (arr _A _P _D, arr _A _A _D) with true in
-- utest subtype (arr _A _A _D, arr _P _A _D) with true in
--
-- let arr = lam c.
--   tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) c _D
-- in
--
-- utest subtype (arr _A, arr _A) with true in
-- utest subtype (arr _PC, arr _A) with true in
-- utest subtype (arr _P, arr _A) with true in
-- utest subtype (arr _C, arr _A) with true in
-- utest subtype (arr _M, arr _A) with true in
--
-- utest subtype (arr _A, arr _PC) with false in
-- utest subtype (arr _PC, arr _PC) with true in
-- utest subtype (arr _P, arr _PC) with true in
-- utest subtype (arr _C, arr _PC) with true in
-- utest subtype (arr _M, arr _PC) with true in
--
-- utest subtype (arr _A, arr _P) with false in
-- utest subtype (arr _PC, arr _P) with false in
-- utest subtype (arr _P, arr _P) with true in
-- utest subtype (arr _C, arr _P) with false in
-- utest subtype (arr _M, arr _P) with true in
--
-- utest subtype (arr _A, arr _C) with false in
-- utest subtype (arr _PC, arr _C) with false in
-- utest subtype (arr _P, arr _C) with false in
-- utest subtype (arr _C, arr _C) with true in
-- utest subtype (arr _M, arr _C) with true in
--
-- utest subtype (arr _A, arr _M) with false in
-- utest subtype (arr _PC, arr _M) with false in
-- utest subtype (arr _P, arr _M) with false in
-- utest subtype (arr _C, arr _M) with false in
-- utest subtype (arr _M, arr _M) with true in
--
-- -- Type variables
-- utest subtype (tyvar_ "X", tyvar_ "X") with true in
-- utest subtype (tyvar_ "X", tyvar_ "Y") with false in
--
-- -- Distributions
-- let dist = lam c. tydist_ (tyfloatc_ c) in
--
-- utest subtype (dist _A, dist _A) with true in
-- utest subtype (dist _A, dist _P) with false in
--
-- -- ┌────────────────────────┐
-- -- │ Test joinType/meetType │
-- -- └────────────────────────┘
--
-- let eq = optionEq eqType in
--
-- -- Bottom type
-- utest
--   forAll (lam ty.
--     and
--       (eq (joinType (ty, tybot_)) (Some ty))
--       (eq (joinType (tybot_, ty)) (Some ty)))
--     alltypes
--   with true
-- in
--
-- utest meetType (tybot_, tybot_) with (Some tybot_) using eq in
--
-- -- Base types
-- let _joinType = lam c1. lam c2. joinType (tyfloatc_ c1, tyfloatc_ c2) in
--
-- utest _joinType _A _A  with Some (tyfloatc_ _A)  using eq in
-- utest _joinType _A _PC with Some (tyfloatc_ _A)  using eq in
-- utest _joinType _PC _A with Some (tyfloatc_ _A)  using eq in
-- utest _joinType _A _P  with Some (tyfloatc_ _A)  using eq in
-- utest _joinType _P _A  with Some (tyfloatc_ _A)  using eq in
-- utest _joinType _C _A  with Some (tyfloatc_ _A)  using eq in
-- utest _joinType _A _C  with Some (tyfloatc_ _A)  using eq in
-- utest _joinType _A _M  with Some (tyfloatc_ _A)  using eq in
-- utest _joinType _M _A  with Some (tyfloatc_ _A)  using eq in
-- utest _joinType _PC _P with Some (tyfloatc_ _PC) using eq in
-- utest _joinType _P _PC with Some (tyfloatc_ _PC) using eq in
-- utest _joinType _PC _C with Some (tyfloatc_ _PC) using eq in
-- utest _joinType _C _PC with Some (tyfloatc_ _PC) using eq in
-- utest _joinType _PC _M with Some (tyfloatc_ _PC) using eq in
-- utest _joinType _M _PC with Some (tyfloatc_ _PC) using eq in
-- utest _joinType _P _P  with Some (tyfloatc_ _P)  using eq in
-- utest _joinType _P _C  with Some (tyfloatc_ _PC) using eq in
-- utest _joinType _C _P  with Some (tyfloatc_ _PC) using eq in
-- utest _joinType _P _M  with Some (tyfloatc_ _P)  using eq in
-- utest _joinType _M _P  with Some (tyfloatc_ _P)  using eq in
-- utest _joinType _C _C  with Some (tyfloatc_ _C)  using eq in
-- utest _joinType _C _M  with Some (tyfloatc_ _C)  using eq in
-- utest _joinType _M _C  with Some (tyfloatc_ _C)  using eq in
-- utest _joinType _M _M  with Some (tyfloatc_ _M)  using eq in
--
-- let _meetType = lam c1. lam c2. meetType (tyfloatc_ c1, tyfloatc_ c2) in
--
-- utest _meetType _A _A  with Some (tyfloatc_ _A)  using eq in
-- utest _meetType _A _PC with Some (tyfloatc_ _PC) using eq in
-- utest _meetType _PC _A with Some (tyfloatc_ _PC) using eq in
-- utest _meetType _A _P  with Some (tyfloatc_ _P)  using eq in
-- utest _meetType _P _A  with Some (tyfloatc_ _P)  using eq in
-- utest _meetType _C _A  with Some (tyfloatc_ _C)  using eq in
-- utest _meetType _A _C  with Some (tyfloatc_ _C)  using eq in
-- utest _meetType _A _M  with Some (tyfloatc_ _M)  using eq in
-- utest _meetType _M _A  with Some (tyfloatc_ _M)  using eq in
-- utest _meetType _PC _P with Some (tyfloatc_ _P)  using eq in
-- utest _meetType _P _PC with Some (tyfloatc_ _P)  using eq in
-- utest _meetType _PC _C with Some (tyfloatc_ _C)  using eq in
-- utest _meetType _C _PC with Some (tyfloatc_ _C)  using eq in
-- utest _meetType _PC _M with Some (tyfloatc_ _M)  using eq in
-- utest _meetType _M _PC with Some (tyfloatc_ _M)  using eq in
-- utest _meetType _P _P  with Some (tyfloatc_ _P)  using eq in
-- utest _meetType _P _C  with Some (tyfloatc_ _M) using eq in
-- utest _meetType _C _P  with Some (tyfloatc_ _M) using eq in
-- utest _meetType _P _M  with Some (tyfloatc_ _M)  using eq in
-- utest _meetType _M _P  with Some (tyfloatc_ _M)  using eq in
-- utest _meetType _C _C  with Some (tyfloatc_ _C)  using eq in
-- utest _meetType _C _M  with Some (tyfloatc_ _M)  using eq in
-- utest _meetType _M _C  with Some (tyfloatc_ _M)  using eq in
-- utest _meetType _M _M  with Some (tyfloatc_ _M)  using eq in
--
-- -- Sequences
-- let seq = lam c. tyseq_ (tyfloatc_ c) in
--
-- utest joinType (seq _A, seq _A) with Some (seq _A) using eq in
-- utest joinType (seq _A, seq _P) with Some (seq _A) using eq in
-- utest joinType (seq _P, seq _A) with Some (seq _A) using eq in
-- utest joinType (seq _P, seq _P) with Some (seq _P) using eq in
-- utest meetType (seq _A, seq _A) with Some (seq _A) using eq in
-- utest meetType (seq _A, seq _P) with Some (seq _P) using eq in
-- utest meetType (seq _P, seq _A) with Some (seq _P) using eq in
-- utest meetType (seq _P, seq _P) with Some (seq _P) using eq in
-- utest meetType (seq _P, tyfloatc_ _A) with None () using eq in
--
-- -- Records
-- utest joinType (tup2 _A _A, tup2 _A _A) with Some (tup2 _A _A) using eq in
-- utest joinType (tup2 _A _A, tup3 _A _A _A) with None () using eq in
-- utest joinType (tup3 _A _A _A, tup2 _A _A) with None () using eq in
-- utest joinType (tup2 _P _M, tup2 _A _P) with Some (tup2 _A _P) using eq in
-- utest joinType (tup2 _A _A, tup2 _A _P) with Some (tup2 _A _A) using eq in
--
-- utest meetType (tup2 _A _A, tup2 _A _A) with Some (tup2 _A _A) using eq in
-- utest meetType (tup2 _A _A, tup3 _A _A _A) with None () using eq in
-- utest meetType (tup3 _A _A _A, tup2 _A _A) with None () using eq in
-- utest meetType (tup2 _P _M, tup2 _A _P) with Some (tup2 _P _M) using eq in
-- utest meetType (tup2 _A _A, tup2 _A _P) with Some (tup2 _A _P) using eq in
--
-- -- Arrows
-- let arr = tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) _A in
-- let _joinType = lam e1. lam e2. joinType (arr e1, arr e2) in
--
-- utest _joinType _D _D with Some (arr _D) using eq in
-- utest _joinType _D _R with Some (arr _R) using eq in
-- utest _joinType _R _D with Some (arr _R) using eq in
-- utest _joinType _R _R with Some (arr _R) using eq in
--
-- let _meetType = lam e1. lam e2. meetType (arr e1, arr e2) in
--
-- utest _meetType _D _D with Some (arr _D) using eq in
-- utest _meetType _D _R with Some (arr _D) using eq in
-- utest _meetType _R _D with Some (arr _D) using eq in
-- utest _meetType _R _R with Some (arr _R) using eq in
--
-- let arr = lam c. tyarrowce_ (tyfloatc_ c) (tyfloatc_ _A) _A _D in
-- let _joinType = lam c1. lam c2. joinType (arr c1, arr c2) in
--
-- utest _joinType _A _A with Some (arr _A) using eq in
-- utest _joinType _A _P with Some (arr _P) using eq in
-- utest _joinType _P _A with Some (arr _P) using eq in
--
-- let _meetType = lam c1. lam c2. meetType (arr c1, arr c2) in
--
-- utest _meetType _A _A with Some (arr _A) using eq in
-- utest _meetType _A _P with Some (arr _A) using eq in
-- utest _meetType _P _A with Some (arr _A) using eq in
--
-- let arr = lam c. tyarrowce_ (tyfloatc_ _A) (tyfloatc_ c) _A _D in
-- let _joinType = lam c1. lam c2. joinType (arr c1, arr c2) in
--
-- utest _joinType _A _A with Some (arr _A) using eq in
-- utest _joinType _A _P with Some (arr _A) using eq in
-- utest _joinType _P _A with Some (arr _A) using eq in
--
-- let _meetType = lam c1. lam c2. meetType (arr c1, arr c2) in
--
-- utest _meetType _A _A with Some (arr _A) using eq in
-- utest _meetType _A _P with Some (arr _P) using eq in
-- utest _meetType _P _A with Some (arr _P) using eq in
--
-- let arr = lam c. tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) c _D in
-- let _joinType = lam c1. lam c2. joinType (arr c1, arr c2) in
--
-- utest _joinType _A _A   with Some (arr _A)  using eq in
-- utest _joinType _A _PC  with Some (arr _A)  using eq in
-- utest _joinType _PC _A  with Some (arr _A)  using eq in
-- utest _joinType _A _P   with Some (arr _A)  using eq in
-- utest _joinType _P _A   with Some (arr _A)  using eq in
-- utest _joinType _A _C   with Some (arr _A)  using eq in
-- utest _joinType _C _A   with Some (arr _A)  using eq in
-- utest _joinType _A _M   with Some (arr _A)  using eq in
-- utest _joinType _M _A   with Some (arr _A)  using eq in
-- utest _joinType _PC _PC with Some (arr _PC) using eq in
-- utest _joinType _PC _P  with Some (arr _PC) using eq in
-- utest _joinType _P _PC  with Some (arr _PC) using eq in
-- utest _joinType _PC _C  with Some (arr _PC) using eq in
-- utest _joinType _C _PC  with Some (arr _PC) using eq in
-- utest _joinType _PC _M  with Some (arr _PC) using eq in
-- utest _joinType _M _PC  with Some (arr _PC) using eq in
-- utest _joinType _P _P   with Some (arr _P)  using eq in
-- utest _joinType _P _C   with Some (arr _PC) using eq in
-- utest _joinType _C _P   with Some (arr _PC) using eq in
-- utest _joinType _P _M   with Some (arr _P)  using eq in
-- utest _joinType _M _P   with Some (arr _P)  using eq in
-- utest _joinType _C _C   with Some (arr _C)  using eq in
-- utest _joinType _C _M   with Some (arr _C)  using eq in
-- utest _joinType _M _C   with Some (arr _C)  using eq in
-- utest _joinType _M _M   with Some (arr _M)  using eq in
--
-- let _meetType = lam c1. lam c2. meetType (arr c1, arr c2) in
--
-- utest _meetType _A _A   with Some (arr _A)  using eq in
-- utest _meetType _A _PC  with Some (arr _PC) using eq in
-- utest _meetType _PC _A  with Some (arr _PC) using eq in
-- utest _meetType _A _P   with Some (arr _P)  using eq in
-- utest _meetType _P _A   with Some (arr _P)  using eq in
-- utest _meetType _A _C   with Some (arr _C)  using eq in
-- utest _meetType _C _A   with Some (arr _C)  using eq in
-- utest _meetType _A _M   with Some (arr _M)  using eq in
-- utest _meetType _M _A   with Some (arr _M)  using eq in
-- utest _meetType _PC _PC with Some (arr _PC) using eq in
-- utest _meetType _PC _P  with Some (arr _P)  using eq in
-- utest _meetType _P _PC  with Some (arr _P)  using eq in
-- utest _meetType _PC _C  with Some (arr _C)  using eq in
-- utest _meetType _C _PC  with Some (arr _C)  using eq in
-- utest _meetType _PC _M  with Some (arr _M)  using eq in
-- utest _meetType _M _PC  with Some (arr _M)  using eq in
-- utest _meetType _P _P   with Some (arr _P)  using eq in
-- utest _meetType _P _C   with Some (arr _M)  using eq in
-- utest _meetType _C _P   with Some (arr _M)  using eq in
-- utest _meetType _P _M   with Some (arr _M)  using eq in
-- utest _meetType _M _P   with Some (arr _M)  using eq in
-- utest _meetType _C _C   with Some (arr _C)  using eq in
-- utest _meetType _C _M   with Some (arr _M)  using eq in
-- utest _meetType _M _C   with Some (arr _M)  using eq in
-- utest _meetType _M _M   with Some (arr _M)  using eq in
--
-- -- Type variables
-- utest joinType (tyvar_ "X", tyvar_ "X") with Some (tyvar_ "X") using eq in
-- utest joinType (tyvar_ "X", tyvar_ "Y") with None () using eq in
-- utest meetType (tyvar_ "X", tyvar_ "X") with Some (tyvar_ "X") using eq in
-- utest meetType (tyvar_ "X", tyvar_ "Y") with None () using eq in
--
-- -- Distributions
-- let dist = lam c. tydist_ (tyfloatc_ c) in
--
-- utest joinType (dist _A, dist _A) with Some (dist _A) using eq in
-- utest joinType (dist _A, dist _P) with Some (dist _A) using eq in
-- utest joinType (dist _P, dist _A) with Some (dist _A) using eq in
--
-- utest meetType (dist _A, dist _A) with Some (dist _A) using eq in
-- utest meetType (dist _A, dist _P) with Some (dist _P) using eq in
-- utest meetType (dist _P, dist _A) with Some (dist _P) using eq in
--
-- -- ┌───────────────┐
-- -- │ Test glbcType │
-- -- └───────────────┘
--
-- -- Bottom
-- utest glbcType tybot_ with _A in
--
-- -- Float
-- let _glbcType = lam c. glbcType (tyfloatc_ c) in
--
-- utest _glbcType _A with _A in
-- utest _glbcType _M with _M in
--
-- -- Seqences
-- let _glbcType = lam c. glbcType (tyseq_ (tyfloatc_ c)) in
--
-- utest _glbcType _A with _A in
-- utest _glbcType _M with _M in
--
-- -- Records
-- let _glbcType = lam c1. lam c2. glbcType (tytuple_ [tyfloatc_ c1, tyfloatc_ c2]) in
--
-- utest _glbcType _A _A with _A in
-- utest _glbcType _A _P with _P in
-- utest _glbcType _P _A with _P in
--
-- -- Arrows
-- let _glbcType = lam c1. lam c2.
--   glbcType (tyarrowce_ (tyfloatc_ c1) (tyfloatc_ c2) _A _D)
-- in
--
-- utest _glbcType _A _A with _A in
-- utest _glbcType _A _P with _A in
-- utest _glbcType _P _A with _A in
--
-- -- Type variables
-- utest glbcType (tyvar_ "X") with _A in
--
-- -- Distributions
-- let _glbcType = lam c. glbcType (tydist_ (tyfloatc_ c)) in
--
-- utest _glbcType _A with _A in
-- utest _glbcType _M with _A in
--
-- -- ┌────────────────────────────┐
-- -- │ Test dtcEnvGlbc/dtcEnvLubc │
-- -- └────────────────────────────┘
--
-- let genC = lam.
--   switch randIntU 0 5
--   case 0 then ModA ()
--   case 1 then ModPC ()
--   case 2 then _P
--   case 3 then _C
--   case 4 then _M
--   end
-- in
--
-- let genEnv = lam.
--   dtcEnvOfSeq [
--     (_x, tyfloatc_ (genC ())),
--     (_y, tyfloatc_ (genC ())),
--     (_z, tyfloatc_ (genC ())),
--     (_f, tyarrowce_ (tyfloatc_ _A) (tyfloatc_ _A) (genC ()) _D),
--     (_g, tydist_ (tyfloatc_ _A))
--   ]
-- in
--
-- repeat
--   (lam. let env = genEnv () in
--       let minc = dtcEnvGlbc env in
--       let maxc = dtcEnvLubc env in
--       -- Exit on first failing test
--       let onFail = lam. lam.
--         error (strJoin "\n" [
--           "Failed randomized environment test with:",
--           concat "minc: " (dtcRegToString minc),
--           concat "maxc: " (dtcRegToString maxc),
--           concat "env: " (dtcEnvToString env)
--         ])
--       in
--       utest dtcLeqcEnv minc env with true
--         using and else onFail
--       in
--       let allcs = [ModA (), _P, _C, _M] in
--       -- Test that minc is indeed the maximum coeffect modifier that fulfuills
--       -- `dtcLeqcEnv c env`
--       iter (lam c.
--         if not (dtcLeqc c minc) then
--           utest dtcLeqcEnv c env with false
--             using (lam a. lam b. not (or a b)) else onFail
--           in ()
--         else ())
--         allcs;
--       utest dtcLeqEnvc env maxc with true
--         using and else onFail
--       in
--       -- Test that maxc is indeed the minimum coeffect modifier that fulfuills
--       -- `dtcLeqEnvc env c`
--       iter (lam c.
--         if not (dtcLeqc maxc c) then
--           utest dtcLeqEnvc env c with false
--             using (lam a. lam b. not (or a b)) else onFail
--           in ()
--         else ())
--         allcs)
--   1000;
--
-- -- ┌─────────────┐
-- -- │ Test typeOf │
-- -- └─────────────┘
--
-- let _typeOf = lam env. lam tm. (result.consume (typeOf (dtcEnvOfSeq env) tm)).1 in
--
-- let eq =
--   -- Either compare the type or the error constructors
--   eitherEq
--     (lam l. lam r.
--       forAll (lam x. x)
--         (zipWith (lam l. lam r. eqi (constructorTag l) (constructorTag r)) l r))
--     (tupleEq2 dtcEqe eqType)
-- in
--
-- let toString =
--   eitherEither
--     (lam errs. strJoin "\n" (map typeErrorToString errs))
--     (lam t. join [":", dtcEffectToString t.0, " ", type2str t.1])
-- in
-- let onFail = utestDefaultToString toString toString in
--
-- -- Shorthand types
-- let arrce = lam ps. lam ret. foldr (lam t. lam to. tyarrowce_ t.0 to t.1 t.2) ret ps in
-- let arrc = lam ps. arrce (map (lam p. (p.0, p.1, _D)) ps) in
-- let arre = lam ps. arrce (map (lam p. (p.0, _A, p.1)) ps) in
-- let arr = lam ps. arrce (map (lam p. (p, _A, _D)) ps) in
-- let flt = tyfloatc_ in
--
-- -- Shorthand terms
-- let lam_ = nlams_ in
-- let f = appSeq_ (nvar_ _f) in
-- let g = appSeq_ (nvar_ _g) in
-- let h = appSeq_ (nvar_ _h) in
-- let x = nvar_ _x in
-- let y = nvar_ _y in
-- let z = nvar_ _z in
-- let u = nvar_ _u in
-- let v = nvar_ _v in
-- let w = nvar_ _w in
--
-- -- Basic tests
-- utest _typeOf [] (lam_ [(_x, tyint_)] x)
--   with Right (_D, arrc [(tyint_, _M)] tyint_)
--   using eq else onFail
-- in
--
-- utest _typeOf [(_x, tyint_)] (app_ x x)
--   with Left [DTCArrowError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest _typeOf [(_x, tyint_)] (bind_ (nulet_ _y x) y)
--   with Right (_D, tyint_)
--   using eq else onFail
-- in
--
-- -- Test effect propagation
-- utest _typeOf [(_f, arrce [(tyint_, _A, _R)] tyint_), (_x, tyint_)] (f [x])
--   with Right (_R, tyint_)
--   using eq else onFail
-- in
--
-- -- Test subtyping and promotion
-- utest _typeOf [(_f, arr [flt _A] (flt _A)), (_x, flt _A)] (f [x])
--   with Right (_D, flt _A)
--   using eq else onFail
-- in
--
-- utest _typeOf [(_f, arr [flt _A] (flt _A)), (_x, flt _P)] (f [x])
--   with Right (_D, flt _A)
--   using eq else onFail
-- in
--
-- utest _typeOf [(_f, arr [flt _A] tyint_), (_x, tyint_)] (f [x])
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- let env = [
--   (_f, arrc [(flt _A, _P), (flt _A, _A)] (flt _A)),
--   (_g, arrc [(flt _P, _A), (flt _P, _A)] (flt _P)),
--   (_x, flt _P),
--   (_y, flt _A)
-- ] in
--
-- utest
--   _typeOf env  (f [f [x, x], x])
--   with Right (_D, flt _P)
--   using eq else onFail
-- in
--
-- utest
--   _typeOf env  (f [g [f [x, x], x], y])
--   with Right (_D, flt _A)
--   using eq else onFail
-- in
--
-- utest
--   _typeOf env (f [g [f [x, x], y], y])
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _typeOf env (f [g [f [x, y], x], y])
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _typeOf [] (addf_ (float_ 1.) (float_ 1.))
--   with Right (_D, flt _M)
--   using eq else onFail
-- in
--
-- let env = [
--   (_f, arrc [(flt _A, _M)] (flt _A)),
--   (_g, arr [flt _M] (flt _M))
-- ] in
--
-- utest
--   _typeOf env
--     (app_
--        (lam_ [(_h, arr [flt _A] (flt _M))] (lam_ [(_y, flt _A)] (g [h [y]])))
--        (lam_ [(_x, flt _A)] (f [float_ 1.])))
--   with Right (_D, arr [flt _A] (flt _M))
--   using eq else onFail
-- in
--
-- let env = [
--   (_f, arr [flt _M, flt _M] (flt _M)),
--   (_x, flt _M),
--   (_y, flt _A)
-- ] in
--
-- utest
--   _typeOf env (addf_ (f [addf_ x (float_ 1.), x]) y)
--   with Right (_D, flt _A)
--   using eq else onFail
-- in
--
-- let env = [
--   (_f, arr [flt _M, flt _M] (flt _M)),
--   (_x, flt _P),
--   (_y, flt _A)
-- ] in
--
-- utest
--   _typeOf env (addf_ (f [addf_ x (float_ 1.), x]) y)
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- -- Test sequence
--
-- utest
--   _typeOf [] (seq_ [])
--   with Right (_D, tyseq_ (TyBot { info = NoInfo () }))
--   using eq else onFail
-- in
--
-- utest
--   _typeOf [(_x, flt _A)] (seq_ [x])
--   with Right (_D, tyseq_ (flt _A))
--   using eq else onFail
-- in
--
-- utest
--   _typeOf [(_x, flt _A), (_y, flt _P)] (seq_ [x, y])
--   with Right (_D, tyseq_ (flt _A))
--   using eq else onFail
-- in
--
-- utest
--   _typeOf [
--     (_f, arre [(flt _A, _R)] (flt _A)),
--     (_g, arre [(flt _A, _D)] (flt _A)),
--     (_x, flt _P),
--     (_y, flt _M)
--   ] (seq_ [f [x], g [y]])
--   with Right (_R, tyseq_ (flt _A))
--   using eq else onFail
-- in
--
-- -- Test records
--
-- utest
--   _typeOf [] (utuple_ [])
--   with Right (_D, tytuple_ [])
--   using eq else onFail
-- in
--
-- utest
--   _typeOf [(_x, flt _A), (_y, flt _P)] (utuple_ [x, y])
--   with Right (_D, tytuple_ [flt _A, flt _P])
--   using eq else onFail
-- in
--
-- utest
--   _typeOf [
--     (_f, arrce [(flt _A, _P,  _R)] (flt _A)),
--     (_g, arrce [(flt _A, _M, _D)] (flt _A)),
--     (_x, flt _P),
--     (_y, flt _M)
--   ] (utuple_ [f [x], g [y]])
--   with Right (_R, tytuple_ [flt _P, flt _M])
--   using eq else onFail
-- in
--
-- -- Test never
--
-- utest _typeOf [] never_ with Right (_D, tybot_) using eq else onFail in
--
-- -- Test match
--
-- let env = [
--   (_x, flt _A)
-- ] in
--
-- utest
--   _typeOf env (match_ x (npvar_ _y) y x)
--   with Right (_D, flt _A)
--   using eq else onFail
-- in
--
-- utest
--   _typeOf env (match_ x (npvar_ _y) y (float_ 1.))
--   with Right (_D, flt _A)
--   using eq else onFail
-- in
--
-- let env = [
--   (_f, arrce [(flt _P, _M, _D), (flt _P, _P, _D)] (flt _A)),
--   (_g, arrce [(flt _A, _P, _R), (flt _M, _A, _D)] (flt _P))
-- ] in
--
-- utest
--   let f = nvar_ _f in
--   let g = nvar_ _g in
--   _typeOf env (match_ f pvarw_ f g)
--   with Left [DTCHigherOrderTypeError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- let env = [
--   (_x, tyseq_ (flt _A))
-- ] in
--
-- utest
--   _typeOf env (match_ x (pseqtot_ [npvar_ _y, npvar_ _z]) (seq_ [z, y]) x)
--   with Right (_D, tyseq_ (flt _A))
--   using eq else onFail
-- in
--
-- utest
--   _typeOf env
--     (match_ x (pseqedgen_ [npvar_ _y] _z [npvar_ _u])
--        (concat_ z (seq_ [y, u])) x)
--   with Right (_D, tyseq_ (flt _A))
--   using eq else onFail
-- in
--
-- let env = [
--   (_x, tytuple_ [flt _A, flt _P, flt _M])
-- ] in
--
-- utest
--   _typeOf env (tupleproj_ 0 x)
--   with Right (_D, flt _A)
--   using eq else onFail
-- in
--
-- utest
--   _typeOf env (tupleproj_ 1 x)
--   with Right (_D, flt _P)
--   using eq else onFail
-- in
--
-- utest
--   _typeOf env (tupleproj_ 2 x)
--   with Right (_D, flt _M)
--   using eq else onFail
-- in
--
-- utest
--   _typeOf env (tupleproj_ 3 x)
--   with Left [DTCPatError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _typeOf [(_x, tyint_)] (match_ x (pint_ 0) x x)
--   with Right (_D, tyint_)
--   using eq else onFail
-- in
--
-- utest
--   _typeOf [(_x, tychar_)] (match_ x (pchar_ '0') x x)
--   with Right (_D, tychar_)
--   using eq else onFail
-- in
--
-- utest
--   _typeOf [(_x, tybool_)] (match_ x ptrue_ x x)
--   with Right (_D, tybool_)
--   using eq else onFail
-- in
--
-- utest
--   _typeOf [(_x, tychar_)] (match_ x (pint_ 0) x x)
--   with Left [DTCPatError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _typeOf [(_x, tybool_)] (match_ x (pchar_ '0') x x)
--   with Left [DTCPatError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _typeOf [(_x, tyint_)] (match_ x ptrue_ x x)
--   with Left [DTCPatError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- let env = [
--   (_x, flt _A),
--   (_y, flt _P)
-- ] in
--
-- let _tm = lam pat.
--   match_ (utuple_ [x, y])
--     (pat (ptuple_ [npvar_ _z, pvarw_]) (ptuple_ [pvarw_, npvar_ _z]))
--     z never_
-- in
--
-- utest _typeOf env (_tm pand_)
--   with Right (_D, flt _A)
--   using eq else onFail
-- in
--
-- utest _typeOf env (_tm por_)
--   with Right (_D, flt _A)
--   using eq else onFail
-- in
--
-- let _tm = match_ x (pnot_ (pint_ 0)) x x in
--
-- utest _typeOf [(_x, tyint_)] _tm
--   with Right (_D, tyint_)
--   using eq else onFail
-- in
--
-- utest _typeOf [(_x, flt _A)] _tm
--   with Left [DTCPatError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- -- Infer
--
-- let env = [(_f, arrc [(tyunit_, _M)] (flt _A))] in
-- let infer__ = infer_ (Default { runs = int_ 1 }) in
--
-- utest _typeOf env (infer__ (nvar_ _f))
--   with Right (_D, tydist_ (flt _A))
--   using eq else onFail
-- in
--
-- utest _typeOf [(_f, arrc [(flt _A, _M)] (flt _A))] (infer__ (nvar_ _f))
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- let infer__ = infer_ (Default { runs = never_ }) in
--
-- utest _typeOf env (infer__ (nvar_ _f))
--   with Right (_D, tydist_ (flt _A))
--   using eq else onFail
-- in
--
-- utest
--   _typeOf
--     (concat env [(_x, arr [flt _M] tyint_), (_y, flt _A)])
--     (infer_ (Default { runs = app_ x y }) (nvar_ _f))
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _typeOf
--     (concat env [(_x, arre [(flt _A, _R)] tyint_), (_y, flt _A)])
--     (infer_ (Default { runs = app_ x y }) (nvar_ _f))
--   with Right (_R, tydist_ (flt _A))
--   using eq else onFail
-- in
--
-- -- Assume
--
-- utest _typeOf [(_x, tydist_ (flt _A))] (assume_ x)
--   with Right (_R, flt _M)
--   using eq else onFail
-- in
--
-- utest _typeOf [(_x, flt _A)] (assume_ x)
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- -- Observe
--
-- utest _typeOf [(_x, tydist_ (flt _A))] (observe_ (float_ 0.) x)
--   with Right (_D, tyunit_)
--   using eq else onFail
-- in
--
-- utest _typeOf [(_x, tydist_ (flt _A))] (observe_ (int_ 0) x)
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest _typeOf [(_x, flt _A)] (observe_ (float_ 0.) x)
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- -- Weight
--
-- utest _typeOf [(_x, flt _A)] (weight_ x)
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest _typeOf [(_x, flt _P)] (weight_ x)
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest _typeOf [(_x, flt _M)] (weight_ x)
--   with Right (_R, tyunit_)
--   using eq else onFail
-- in
--
-- utest _typeOf [] (weight_ (int_ 0))
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- -- Dist
--
-- utest _typeOf [(_x, flt _M), (_y, flt _M)] (dist_ (DUniform {a = x, b = y}))
--   with Right (_D, tydist_ (flt _M))
--   using eq else onFail
-- in
--
-- utest _typeOf [(_x, flt _M)] (dist_ (DBernoulli {p = x}))
--   with Right (_D, tydist_ tybool_)
--   using eq else onFail
-- in
--
-- utest _typeOf [(_x, flt _M)] (dist_ (DPoisson {lambda = x}))
--   with Right (_D, tydist_ tyint_)
--   using eq else onFail
-- in
--
-- utest _typeOf [(_x, flt _M), (_y, flt _M)] (dist_ (DBeta {a = x, b = y}))
--   with Right (_D, tydist_ (flt _M))
--   using eq else onFail
-- in
--
-- utest _typeOf [(_x, flt _M), (_y, flt _M)] (dist_ (DGamma {k = x, theta = y}))
--   with Right (_D, tydist_ (flt _M))
--   using eq else onFail
-- in
--
-- utest _typeOf [(_x, tyseq_ (flt _M))] (dist_ (DCategorical {p = x}))
--   with Right (_D, tydist_ tyint_)
--   using eq else onFail
-- in
--
-- utest _typeOf [(_x, tyint_), (_y, tyseq_ (flt _M))]
--         (dist_ (DMultinomial {n = x, p = y}))
--   with Right (_D, tydist_ (tyseq_ tyint_))
--   using eq else onFail
-- in
--
-- utest _typeOf [(_x, flt _M)] (dist_ (DExponential {rate = x}))
--   with Right (_D, tydist_ (flt _M))
--   using eq else onFail
-- in
--
-- utest _typeOf [(_x, flt _M), (_y, flt _M)] (dist_ (DGaussian {mu = x, sigma = y}))
--   with Right (_D, tydist_ (flt _M))
--   using eq else onFail
-- in
--
-- utest _typeOf [] (dist_ (DWiener { cps = false, a = unit_ }))
--   with Right (_D, tydist_ (arrc [(flt _C, _M)] (flt _A)))
--   using eq else onFail
-- in
--
-- utest _typeOf [(_x, flt _M)] (dist_ (DExponential {rate = x}))
--   with Right (_D, tydist_ (flt _M))
--   using eq else onFail
-- in
--
-- utest _typeOf [(_x, (tyseq_ (tytuple_ [flt _M, flt _M])))]
--         (dist_ (DEmpirical {samples = x}))
--   with Left [DTCPolyDistError (NoInfo ())]
--   using eq else onFail
-- in
--
-- let _test = lam c.
--   _typeOf [(_x, flt c)] (dist_ (DExponential {rate = x}))
-- in
--
-- utest _test _A
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest _test _P
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- -- Diff
--
-- let _test = lam c1. lam c2. lam c3. lam c4. lam c5. lam e. _typeOf [
--   (_x, arrce [(flt c1, c2, e)] (flt c3)),
--   (_y, flt c4),
--   (_z, flt c5)
-- ] (TmDiff {
--   fn = x,
--   arg = y,
--   darg = z,
--   ty = tyunknown_,
--   info = NoInfo ()
-- }) in
--
-- utest
--   _test _A _P _A _A _A _D
--   with Right (_D, flt _A)
--   using eq else onFail
-- in
--
-- utest
--   _test _A _PC _A _A _A _D
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _test _A _C _A _A _A _D
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _test _A _M _A _A _A _D
--   with Right (_D, flt _A)
--   using eq else onFail
-- in
--
-- utest
--   _test _A _P _A _P _P _D
--   with Right (_D, flt _P)
--   using eq else onFail
-- in
--
-- utest
--   _test _A _P _A _C _C _D
--   with Right (_D, flt _PC)
--   using eq else onFail
-- in
--
-- utest
--   _test _A _P _A _M _M _D
--   with Right (_D, flt _P)
--   using eq else onFail
-- in
--
-- utest
--   _test _A _P _P _A _A _D
--   with Right (_D, flt _A)
--   using eq else onFail
-- in
--
-- utest
--   _test _A _P _C _A _A _D
--   with Right (_D, flt _A)
--   using eq else onFail
-- in
--
-- utest
--   _test _A _P _M _A _A _D
--   with Right (_D, flt _A)
--   using eq else onFail
-- in
--
-- utest
--   _test _P _P _A _A _A _D
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _test _M _P _A _A _A _D
--   with Left [DTCDiffFnError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _test _A _P _A _A _A _R
--   with Left [DTCDiffFnError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _test _P _P _A _A _A _D
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _test _P _P _A _P _A _D
--   with Right (_D, flt _A)
--   using eq else onFail
-- in
--
-- utest
--   _test _P _P _A _C _A _D
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _test _P _P _A _M _A _D
--   with Right (_D, flt _A)
--   using eq else onFail
-- in
--
-- utest
--   _test _M _P _A _P _A _D
--   with Left [DTCDiffFnError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _test _M _P _A _M _A _D
--   with Left [DTCDiffFnError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _typeOf [
--     (_x, arr [tyseq_ (tytuple_ [flt _A, tyint_])] (flt _A)),
--     (_y, (tyseq_ (tytuple_ [flt _A, tyint_]))),
--     (_z, (tyseq_ (tytuple_ [flt _A, tyint_])))
--   ] (diff_ x y z)
--   with Left [DTCDiffFnError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _typeOf [
--     (_x, arr [flt _A] (tyseq_ (tytuple_ [flt _A, tyint_]))),
--     (_y, (flt _A)),
--     (_z, (flt _A))
--   ] (diff_ x y z)
--   with Left [DTCDiffFnError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- -- Solve
--
-- let _test = lam r.
--   _typeOf [
--     (_x, arrc [(flt r.x, r.arrc1), (flt r.y, r.arrc2)] (flt r.ret)),
--     (_y, tytuple_ [flt r.x0, flt r.y0]),
--     (_z, flt r.x1)
--   ] (solveode_ x y z)
-- in
--
-- utest
--   _test {
--     x = _A,
--     arrc1 = _A,
--     y = _A,
--     arrc2 = _A,
--     ret = _A,
--     x0 = _A,
--     y0 = _A,
--     x1 = _A }
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _test {
--     x = _A,
--     arrc1 = _A,
--     y = _A,
--     arrc2 = _A,
--     ret = _A,
--     x0 = _A,
--     y0 = _A,
--     x1 = _P }
--   with Right (_D, tytuple_ [flt _A, flt _A])
--   using eq else onFail
-- in
--
-- utest
--   _test {
--     x = _C,
--     arrc1 = _A,
--     y = _A,
--     arrc2 = _A,
--     ret = _A,
--     x0 = _A,
--     y0 = _A,
--     x1 = _P }
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _test {
--     x = _C,
--     arrc1 = _A,
--     y = _A,
--     arrc2 = _A,
--     ret = _A,
--     x0 = _A,
--     y0 = _A,
--     x1 = _C }
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _test {
--     x = _C,
--     arrc1 = _A,
--     y = _A,
--     arrc2 = _A,
--     ret = _A,
--     x0 = _C,
--     y0 = _A,
--     x1 = _C }
--   with Right (_D, tytuple_ [flt _A, flt _A])
--   using eq else onFail
-- in
--
-- utest
--   _test {
--     x = _M,
--     arrc1 = _A,
--     y = _A,
--     arrc2 = _A,
--     ret = _A,
--     x0 = _M,
--     y0 = _A,
--     x1 = _M }
--   with Left [DTCSolveODEModelError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _test {
--     x = _A,
--     arrc1 = _A,
--     y = _P,
--     arrc2 = _A,
--     ret = _A,
--     x0 = _A,
--     y0 = _P,
--     x1 = _P }
--   with Left [DTCSolveODEModelError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _test {
--     x = _C,
--     arrc1 = _C,
--     y = _A,
--     arrc2 = _A,
--     ret = _A,
--     x0 = _C,
--     y0 = _C,
--     x1 = _C }
--   with Right (_D, tytuple_ [flt _C, flt _C])
--   using eq else onFail
-- in
--

-- -- Dist Operations
--
-- utest
--   _typeOf [
--     (_x, tydist_ tyint_)
--   ] (app_ (uconst_ (CDistEmpiricalSamples ())) x)
--   with Right (_D, tytuple_ [tyseq_ tyint_, tyseq_ (flt _M)])
--   using eq else onFail
-- in
--
-- utest
--   _typeOf [
--     (_x, tydist_ tyint_)
--   ] (app_ (uconst_ (CDistEmpiricalDegenerate ())) x)
--   with Right (_D, tybool_)
--   using eq else onFail
-- in
--
-- utest
--   _typeOf [
--     (_x, tydist_ tyint_)
--   ] (app_ (uconst_ (CDistEmpiricalNormConst ())) x)
--   with Right (_D, flt _M)
--   using eq else onFail
-- in
--
-- utest
--   _typeOf [
--     (_x, tydist_ tyint_)
--   ] (app_ (uconst_ (CDistEmpiricalAcceptRate ())) x)
--   with Right (_D, flt _M)
--   using eq else onFail
-- in
--
-- utest
--   _typeOf [
--     (_x, tydist_ (flt _M))
--   ] (app_ (uconst_ (CDistExpectation ())) x)
--   with Right (_D, flt _M)
--   using eq else onFail
-- in
--
-- -- Utest
--
-- utest _typeOf [(_x, flt _A), (_y, flt _A), (_z, flt _A)] (bind_ (utest_ x y) z)
--   with Right (_D, flt _A)
--   using eq else onFail
-- in
--
-- utest _typeOf [
--   (_x, flt _A),
--   (_y, flt _A),
--   (_z, flt _A),
--   (_u, arr [flt _A, flt _A] tybool_)
-- ] (bind_ (utestu_ x y u) z)
--   with Right (_D, flt _A)
--   using eq else onFail
-- in
--
-- utest _typeOf [
--   (_x, flt _A),
--   (_y, flt _A),
--   (_z, flt _A),
--   (_u, arr [flt _A, flt _A] tybool_),
--   (_v, arr [flt _A, flt _A] tybool_)
-- ] (bind_ (utestuo_ x y u v) z)
--   with Right (_D, flt _A)
--   using eq else onFail
-- in
--
-- -- ┌───────────────────────┐
-- -- │ Modified Old Examples │
-- -- └───────────────────────┘
--
-- -- Example 1
--
-- let env = [
--   (_f, arrc [(flt _M, _M)] (flt _M))
-- ] in
--
-- let _tm = lam c.
--   nlam_ _u (tytuple_ [flt _M, flt c])
--     (matchex_ u (ptuple_ [npvar_ _x, npvar_ _y]) (addf_ (f [x]) y))
-- in
--
-- let _ty = lam c1. lam c2. lam c3.
--   arrc [(tytuple_ [flt _M, flt c1], c3)] (flt c2)
-- in
--
-- utest _typeOf env (_tm _A)
--   with Right (_D, _ty _A _A _M)
--   using eq else onFail
-- in
--
-- utest _typeOf env (_tm _P)
--   with Right (_D, (_ty _P _P _M))
--   using eq else onFail
-- in
--
-- utest _typeOf env (_tm _M)
--   with Right (_D, (_ty _M _M _M))
--   using eq else onFail
-- in
--
-- let _tm = lam c. lam fst. lam snd.
--   nlam_ _z (flt c) (app_ (_tm c) (utuple_ [fst, snd]))
-- in
--
-- let _ty = lam c1. lam c2. lam c3.
--   arrc [(flt c1, c2)] (flt c3)
-- in
--
-- utest _typeOf env (_tm _A (float_ 0.) z)
--   with Right (_D, _ty _A _M _A)
--   using eq else onFail
-- in
--
-- utest _typeOf env (_tm _M z (float_ 0.))
--   with Right (_D, _ty _M _M _M)
--   using eq else onFail
-- in
--
-- utest _typeOf env (_tm _A z (float_ 0.))
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- -- Example 2
--
-- let _tm = lam c. nlam_ _x (flt c) (if_ (gtf_ x (float_ 0.)) x (negf_ x)) in
--
-- utest _typeOf [] (_tm _A)
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest _typeOf [] (_tm _P)
--   with Right (_D, arrc [(flt _P, _M)] (flt _P))
--   using eq else onFail
-- in
--
-- utest _typeOf [] (_tm _M)
--   with Right (_D, arrc [(flt _M, _M)] (flt _M))
--   using eq else onFail
-- in
--
-- -- Example 3
--
-- let expectation_ = app_ (uconst_ (CDistExpectation ())) in
--
-- utest
--   _typeOf [] (nlam_ _x (flt _P) (expectation_ (infer__ (nlam_ _y tyunit_ x))))
--   with Left [DTCArgError (NoInfo (), None ())]
--   using eq else onFail
-- in
--
-- utest
--   _typeOf []
--     (nlam_ _x (flt _P)
--        (mulf_ x (expectation_ (infer__ (nlam_ _y tyunit_ (float_ 1.))))))
--   with Right (_D, arrc [(flt _P, _M)] (flt _P))
--   using eq else onFail
-- in

()
