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
con D : () -> DTCEffect
con R : () -> DTCEffect

let dtcEffectToString : DTCEffect -> String = lam e.
  switch e
  case D _ then "D"
  case R _ then "R"
  end

-- Less than or equal over effects (e ≤ e), where R < D.
let dtcLeqe : DTCEffect -> DTCEffect -> Bool
  = lam a. lam b.
    switch (a, b)
    case (_, D _) then true
    case (D _, _) then false
    case (R _, _) then true
    case (_, R _) then false
    end

utest dtcLeqe (D ()) (D ()) with true
utest dtcLeqe (D ()) (R ()) with false
utest dtcLeqe (R ()) (D ()) with true
utest dtcLeqe (R ()) (R ()) with true

-- Multiplication over effects (e ⋅ e).
let dtcMule : DTCEffect -> DTCEffect -> DTCEffect
  = lam a. lam b. if dtcLeqe a b then a else b

utest dtcMule (D ()) (D ()) with (D ())
utest dtcMule (D ()) (R ()) with (R ())
utest dtcMule (R ()) (D ()) with (R ())
utest dtcMule (R ()) (R ()) with (R ())

-- Equality over effects (e = e).
let dtcEqe : DTCEffect -> DTCEffect -> Bool
  = lam a. lam b.
    switch (a, b)
    case (D _, D _) | (R _, R _) then true
    case _ then false
    end

utest dtcEqe (D ()) (D ()) with true
utest dtcEqe (D ()) (R ()) with false
utest dtcEqe (R ()) (D ()) with false
utest dtcEqe (R ()) (R ()) with true

-- Coeffects are either analytic (A), piecewise analytic under analytic
-- partitioning (P), or measurable (M).
type DTCCoeffect
con A : () -> DTCCoeffect
con P : () -> DTCCoeffect
con M : () -> DTCCoeffect

let dtcCoeffectToString : DTCCoeffect -> String = lam c.
  switch c
  case A _ then "A"
  case P _ then "P"
  case M _ then "M"
  end

let _dtcCoeffectToInt : DTCCoeffect -> Int = lam c.
  switch c
  case M _ then 0
  case P _ then 1
  case A _ then 2
  end

-- Less than or equal over coeffects (c ≤ c), where M < P < A.
let dtcLeqc : DTCCoeffect -> DTCCoeffect -> Bool
  = lam a. lam b. leqi (_dtcCoeffectToInt a) (_dtcCoeffectToInt b)

utest dtcLeqc (A ()) (A ()) with true
utest dtcLeqc (A ()) (P ()) with false
utest dtcLeqc (A ()) (M ()) with false
utest dtcLeqc (P ()) (A ()) with true
utest dtcLeqc (P ()) (P ()) with true
utest dtcLeqc (P ()) (M ()) with false
utest dtcLeqc (M ()) (A ()) with true
utest dtcLeqc (M ()) (P ()) with true
utest dtcLeqc (M ()) (M ()) with true

-- Equality over coeffects (c = c).
let dtcEqc : DTCCoeffect -> DTCCoeffect -> Bool
  = lam a. lam b.
    switch (a, b)
    case (A _, A _) | (P _, P _) | (M _, M _) then true
    case _ then false
    end

utest dtcEqc (A ()) (A ()) with true
utest dtcEqc (A ()) (P ()) with false
utest dtcEqc (A ()) (M ()) with false
utest dtcEqc (P ()) (A ()) with false
utest dtcEqc (P ()) (P ()) with true
utest dtcEqc (P ()) (M ()) with false
utest dtcEqc (M ()) (A ()) with false
utest dtcEqc (M ()) (P ()) with false
utest dtcEqc (M ()) (M ()) with true

-- Min over coeffects (min(c,c)).
let dtcMinc : DTCCoeffect -> DTCCoeffect -> DTCCoeffect
  = lam a. lam b. if dtcLeqc a b then a else b

utest dtcMinc (A ()) (A ()) with (A ())
utest dtcMinc (A ()) (P ()) with (P ())
utest dtcMinc (A ()) (M ()) with (M ())
utest dtcMinc (P ()) (A ()) with (P ())
utest dtcMinc (P ()) (P ()) with (P ())
utest dtcMinc (P ()) (M ()) with (M ())
utest dtcMinc (M ()) (A ()) with (M ())
utest dtcMinc (M ()) (P ()) with (M ())
utest dtcMinc (M ()) (M ()) with (M ())

-- Max over coeffects (max(c,c)).
let dtcMaxc : DTCCoeffect -> DTCCoeffect -> DTCCoeffect
  = lam a. lam b. if dtcLeqc a b then b else a

utest dtcMaxc (A ()) (A ()) with (A ())
utest dtcMaxc (A ()) (P ()) with (A ())
utest dtcMaxc (A ()) (M ()) with (A ())
utest dtcMaxc (P ()) (A ()) with (A ())
utest dtcMaxc (P ()) (P ()) with (P ())
utest dtcMaxc (P ()) (M ()) with (P ())
utest dtcMaxc (M ()) (A ()) with (A ())
utest dtcMaxc (M ()) (P ()) with (P ())
utest dtcMaxc (M ()) (M ()) with (M ())

-- Multiplication over coeffects (c ⋅ c).
let dtcMulc : DTCCoeffect -> DTCCoeffect -> DTCCoeffect = dtcMinc

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
  sem eqcType c =| ty -> dtcEqc c (M ())

  -- "Scalar multiplication" of coeffects over types (c ⋅ T).
  sem mulcType : DTCCoeffect -> Type -> Type
  sem mulcType c =| ty -> ty

  -- Maximum coeffect modifier of type (types that do not represent vectors are
  -- assumed to have `M` modifiers).
  sem maxcType : Type -> DTCCoeffect
  sem maxcType =| _ -> M ()

  -- Minimum coeffect modifier of type (types that do not represent vectors are
  -- assumed to have `A` modifiers).
  sem mincType : Type -> DTCCoeffect
  sem mincType =| _ -> A ()

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
  sem subtype =| (lhs, rhs) ->
    eqi (constructorTag lhs) (constructorTag rhs)

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
  sem fromMExprTy =
  | ty -> smap_Type_Type fromMExprTy ty

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
  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyFloatC (r & {c = A ()}) -> (env, "FloatA")
  | TyFloatC (r & {c = P ()}) -> (env, "FloatP")
  | TyFloatC (r & {c = M ()}) -> (env, "FloatM")

  -- Builder
  sem tyfloatc_ : DTCCoeffect -> Type
  sem tyfloatc_ =| c -> TyFloatC { info = NoInfo (), c = c }

  sem ityfloatc_ : Info -> DTCCoeffect -> Type
  sem ityfloatc_ info =| c -> TyFloatC { info = info, c = c }

  -- Conversions
  sem eraseDecorationsType =
  | TyFloatC r -> TyFloat { info = r.info }

  sem fromMExprTy =
  | TyFloat r -> ityfloatc_ r.info (M ())

  -- Coeffect/Type operations
  sem leqcType c =
  | TyFloatC r -> dtcLeqc c r.c

  sem leqTypecH =
  | (TyFloatC r, c) -> dtcLeqc r.c c

  sem eqcType c =
  | TyFloatC r -> dtcEqc c r.c

  sem mulcType c =
  | TyFloatC r -> TyFloatC { r with c = dtcMulc c r.c }

  sem maxcType =
  | TyFloatC r -> r.c

  sem mincType =
  | TyFloatC r -> r.c

  sem subtype =
  | (TyFloatC l, TyFloatC r) -> dtcLeqc l.c r.c

  sem joinType =
  | (TyFloatC l, TyFloatC r) ->
    Some (if dtcLeqc r.c l.c then TyFloatC l else TyFloatC r)

  sem meetType =
  | (TyFloatC l, TyFloatC r) ->
    Some (if dtcLeqc r.c l.c then TyFloatC r else TyFloatC l)

  sem setC : DTCCoeffect -> Type -> Type
  sem setC c =
  | TyFloatC r -> TyFloatC { r with c = c }
  | ty -> smap_Type_Type (setC c) ty
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
    match printTypeParen indent 1 env r.from with (env, from) in
    match getTypeStringCode indent env r.to with (env, to) in
    switch (r.c, r.e)
    case (A _, D _) then (env, join [from, " -> ", to])
    case (A _, e) then (env, join [from, " ->", dtcEffectToString e, " ", to])
    case (c, D _) then (env, join [from, " ->", dtcCoeffectToString c, " ", to])
    case (c, e) then (env, join [
      from, " ->", dtcCoeffectToString c, ",", dtcEffectToString e, " ", to ])
    end

  -- Builder
  sem tyarrowe_ : Type -> Type -> DTCCoeffect -> DTCEffect -> Type
  sem tyarrowe_ from to c =| e ->
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
    smap_Type_Type fromMExprTy (ityarrowe_ r.info r.from r.to (A ()) (D ()))

  -- Coeffect/Type operations
  sem leqcType c =
  | TyArrowCE r -> dtcLeqc c r.c

  sem leqTypecH =
  | (TyArrowCE r, c) -> dtcLeqc r.c c

  sem eqcType c =
  | TyArrowCE r -> dtcEqc c r.c

  sem mulcType c =
  | TyArrowCE r -> TyArrowCE { r with c = dtcMulc c r.c }

  sem maxcType =
  | TyArrowCE r -> r.c

  sem mincType =
  | TyArrowCE r -> r.c

  sem subtype c =
  | (TyArrowCE l, TyArrowCE r) ->
    allb [
      subtype (r.from, l.from),
      subtype (l.to, r.to),
      dtcLeqc l.c r.c,
      dtcLeqe r.e l.e
    ]

  sem joinType =
  | (TyArrowCE l, TyArrowCE r) ->
    optionBind (meetType (l.from, r.from)) (lam from.
      optionBind (joinType (l.to, r.to)) (lam to.
        Some
          (TyArrowCE
            (if and (dtcLeqc l.c r.c) (dtcLeqe r.e l.e) then
              { r with from = from, to = to }
             else { l with from = from, to = to }))))

  sem meetType =
  | (TyArrowCE l, TyArrowCE r) ->
    optionBind (joinType (l.from, r.from)) (lam from.
      optionBind (meetType (l.to, r.to)) (lam to.
        Some
          (TyArrowCE
            (if and (dtcLeqc l.c r.c) (dtcLeqe r.e l.e) then
              { l with from = from, to = to }
             else { r with from = from, to = to }))))
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

  sem maxcType =
  | TySeq r -> maxcType r.ty

  sem mincType =
  | TySeq r -> mincType r.ty

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

  sem maxcType =
  | ty & TyRecord _ ->
    sfold_Type_Type (lam c. lam ty. dtcMaxc c (maxcType ty)) (M ()) ty

  sem mincType =
  | ty & (TyRecord _) ->
    sfold_Type_Type (lam c. lam ty. dtcMinc c (mincType ty)) (A ()) ty

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

  -- Returns the minimum coeffect modifier of the type environment. I.e., the
  -- maximum coeffect modifier `c` s.t. c ≤ Γ.
  sem dtcEnvMinc : DTCEnv -> DTCCoeffect
  sem dtcEnvMinc =| env ->
    mapFoldWithKey (lam c. lam. lam ty. dtcMinc c (mincType ty)) (A ()) env

  -- Returns the maximum coeffect modifier of the type environment. I.e., the
  -- minumum coeffect modifier `c` s.t. Γ ≤ c.
  sem dtcEnvMaxc : DTCEnv -> DTCCoeffect
  sem dtcEnvMaxc =| env ->
    mapFoldWithKey (lam c. lam. lam ty. dtcMaxc c (maxcType ty)) (M ()) env

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
  | DTCArrowError (Option (Info, Type))
  | DTCArgError (Option (Info, (Type, Type)))
  | DTCJoinError (Option (Info, (Type, Type)))
  | DTCPatError (Option (Info, Type))
  | DTCAnotError (Option Info)
  | DTCSolveODEModelError (Option (Info, Type))
  | DTCDiffFnError (Option (Info, DTCCoeffect, Type))
  | DTCPolyDistError (Option Info)
  | DTCPolyConstError (Option Info)
  | DTCUnuspportedTermError (Option Info)
  | DTCInvalidContextError (Option (Info, Name))
  | DTCContextConstraintError (Option (Info, DTCCoeffect,  DTCEnv))

  sem typeErrorToString : DTCTypeError -> String
  sem typeErrorToString =
  | DTCArrowError _ -> "ArrowError"
  | DTCArgError  _ -> "ArgError"
  | DTCJoinError  _ -> "JoinError"
  | DTCPatError _ -> "PatError"
  | DTCAnotError  _ -> "AnotError"
  | DTCSolveODEModelError _ -> "SolveODEModelError"
  | DTCDiffFnError _ -> "DiffFnError"
  | DTCPolyDistError _ -> "PolyDistError"
  | DTCPolyConstError _ -> "PolyConstError"
  | DTCUnuspportedTermError _ -> "UnuspportedTermError"
  | DTCInvalidContextError _ -> "InvalidContextError"
  | DTCContextConstraintError _ -> "ContextConstraintError"

  sem typeErrorToMsg : DTCTypeError -> (Info, String)
  sem typeErrorToMsg =| err ->
    match typeErrorToMsgH err with (info, msg) in
    (info, join [typeErrorToString err, ":\n", msg])

  sem typeErrorToMsgH : DTCTypeError -> (Info, String)
  sem typeErrorToMsgH =
  | DTCArrowError (Some (info, ty)) ->
    (info, _typeErrorToMsg2 ["Function type"] [type2str ty])
  | DTCArgError (Some (info, (expected, found))) ->
    (info, _typeErrorToMsg2 [type2str expected] [type2str found])
  | DTCJoinError (Some (info, (ty1, ty2))) ->
    (info, join [
      "* Cannot join: ", type2str ty1, "\n",
      "*       with: ", type2str ty2])
  | DTCPatError (Some (info, ty)) ->
    (info, join ["* Pattern does not match type: ", type2str ty])
  | DTCAnotError (Some info) ->
    (info, join ["* Missing type annotation"])
  | DTCSolveODEModelError (Some (info, ty)) ->
    (info,
     _typeErrorToMsg2
       ["Determinstic function type FloatX -> T -> T,",
        join [
          "where T isomorfic to vectors of floats, and X = ",
          dtcCoeffectToString (P ()), " or X = ",
          dtcCoeffectToString (M ()), "."]]
       [type2str ty])
  | DTCDiffFnError (Some (info, c, ty)) ->
    (info,
     _typeErrorToMsg2
       ["Determinstic function type T₁ -> T₂,",
        "where T₁, T₂ are isomorfic to vectors of floats",
        (join ["and where all coeffect modifiers in T₁ are ",
               dtcCoeffectToString c, "."])]
       [type2str ty])
  | DTCPolyDistError (Some info) ->
    (info, "* Polymorfic distributions are currently not supported")
  | DTCPolyConstError (Some info) ->
    (info, join [
      "* Cannot infer the type of this polymorphic intrinsic.\n",
      "* Try to apply it to one or more arguments."
    ])
  | DTCUnuspportedTermError (Some info) ->
    (info, "* This term is currently not supported")
  | DTCInvalidContextError (Some (info, name)) ->
    (info, join [
      "* The variable ", nameGetStr name, " does not appear in the typing context.\n",
      "* This should not happen in symbolized progams."
    ])
  | DTCContextConstraintError (Some (info, c, env)) ->
    (info, join [
      "* The type context ", dtcEnvToString env, "\n",
      "* is not greater or equal to ", dtcCoeffectToString c
    ])
  | _ -> error "Uninformative errors should only appear in test code"

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

  sem promote : DTCEnv -> Set Name -> Type -> Type
  sem promote env =| fv -> let c = dtcEnvMaxc (dtcEnvWeaken fv env) in mulcType c

  sem typeOfH : DTCEnv -> Expr -> Result DTCTypeError DTCTypeError ResultOk
  sem typeOfH env =| tm ->
    result.err (DTCUnuspportedTermError (Some (infoTm tm)))

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
    result.err (DTCArgError (Some (infoTm tm, (ty1, ty2))))

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
           (D (), setEmpty nameCmp)
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
      (lam. result.err (DTCInvalidContextError (Some (r.info, r.ident))))
      (lam ty. result.ok {
        e = D (),
        ty = ty,
        fv = setSingleton nameCmp r.ident })
      (dtcEnvLookup r.ident env)
end

lang DTCTypeOfLam = LamAst + DTCTypeOfBase
  sem typeOfH env =
  | TmLam (r &
    {tyAnnot = TyUnknown _}) ->
    result.err (DTCAnotError (Some r.info))
  | TmLam r ->
    let env = dtcEnvInsert r.ident r.tyAnnot env in
    result.bind (typeOfH env r.body)
      (lam body.
        let promote = promote env body.fv in
        result.ok {
          e = D (),
          ty = promote
                 (ityarrowe_ r.info r.tyAnnot (promote body.ty) (A ()) body.e),
          fv = setRemove r.ident body.fv })
end

lang DTCTypeOfApp = AppAst + DTCFunTypeAst + FreeVars + DTCTypeOfBase
  sem typeOfH env =
  | TmApp r ->
    result.bind (typeOfH env r.lhs) (lam lhs.
      -- NOTE(oerikss, 2025-10-01): Because T1 ->c T2 <: T1 ->A T2 for all c we
      -- do not need to check the coeffect modifier of the arrow type here and
      -- we do not need to promote the LHS.
      match lhs with {ty = TyArrowCE arr} then
        result.bind (typeOfHPromote env r.rhs) (lam rhs.
          if subtype (rhs.ty, arr.from) then
            let fv = setUnion lhs.fv rhs.fv in
            resultOK [lhs.e, arr.e, rhs.e] (promote env fv arr.to) [fv]
          else argErr r.rhs arr.from rhs.ty)
      else result.err (DTCArrowError (Some (infoTm r.lhs, lhs.ty))))
end

lang DTCTypeOfLet = DTCTypeOfLam + DTCTypeOfApp + UnknownTypeAst
  sem typeOfH env =
  | TmDecl (x & {decl = DeclLet r}) ->
    let wi = withInfo r.info in
    typeOfH env (wi (app_ (wi (nlam_ r.ident r.tyAnnot x.inexpr)) r.body))
  | TmDecl (x & {decl = DeclLet (r & {tyAnnot = TyUnknown _})}) ->
    result.bind (typeOfHPromote env r.body) (lam body.
      typeOfH env (TmDecl {x with decl = DeclLet { r with tyAnnot = body.ty }}))
end

lang DTCTyConst = TyConst + DTCTypeError + DTCTypeOfBase

  sem dtcConstType : Info -> Const -> Result DTCTypeError DTCTypeError Type
  sem dtcConstType info =
  | const ->
    -- NOTE(oerikss, 2024-10-09): By default we type constant functions as
    -- deterministic and measurable.
    let ty = fromMExprTy (tyConst const) in
    match ty with TyAll _ then result.err (DTCPolyConstError (Some info))
    else result.ok ty
end

lang DTCTypeOfConst =
  ConstAst + DTCTyConst + CmpFloatAst + ElementaryFunctions +
  DTCFunTypeAst + DTCTypeOfBase

  sem typeOfH env =
  | TmConst r ->
    result.bind (dtcConstType r.info r.val)
      (lam ty. result.ok { e = D (), ty = ty, fv = setEmpty nameCmp })
end

lang DTCTypeOfSeq = SeqAst + SeqTypeAst + DTCTypeOfBase
  sem typeOfH env =
  | TmSeq (r & {tms = []}) ->
    result.ok {
      e = D (),
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
                 (result.err (DTCJoinError (Some (r.info, (ty1, ty2)))))
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
    result.err (DTCPatError (Some (infoPat pat, ty)))

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
    e = D (), ty = TyBot { info = r.info }, fv = setEmpty nameCmp }
end

lang DTCTypeOfMatch = MatchAst + DTCPatTypeCheck + DTCTypeOfBase
  sem typeOfH env =
  | TmMatch r ->
    result.bind (typeOfHPromote env r.target) (lam target.
      result.bind
        (dtcTypeCheckPat env (mapEmpty nameCmp) (target.ty, r.pat))
        (lam patEnv.
          let thnEnv = dtcEnvBatchInsert patEnv env in
          result.bind2 (typeOfHPromote thnEnv r.thn) (typeOfHPromote env r.els)
            (lam thn. lam els.
              optionMapOr
                (result.err (DTCJoinError (Some (r.info, (thn.ty, els.ty)))))
                (lam ty.
                  resultOK [target.e, thn.e, els.e] ty [
                    target.fv,
                    setSubtract thn.fv (setOfKeys patEnv),
                    els.fv
                  ])
                (joinType (thn.ty, els.ty)))))
end

lang DTCTypeOfInfer = Infer + DTCTypeOfBase
  sem typeOfH env =
  | TmInfer r ->
    result.bind2
      (inferSfold_Expr_Expr
         (foldTypeOfH env)
         (result.ok { e = D (), fv = setEmpty nameCmp }) r.method)
      (typeOfH env r.model)
      (lam method. lam model.
        let wenv = dtcEnvWeaken model.fv env in
        if dtcLeqEnvc wenv (M ()) then
          let err =
            argErr r.model
              (tyarrowe_ tyunit_ (tyvar_ "a") (M ()) (R ())) model.ty
          in
          match model with {ty = TyArrowCE (arr & {from = TyRecord rr})} then
            if mapIsEmpty rr.fields then
              resultOK [method.e, model.e]
                (TyDist { info = r.info, ty = arr.to })
                [method.fv, model.fv]
            else err
          else err
        else
          result.err
            (DTCContextConstraintError (Some (infoTm r.model, M (), wenv))))
end

lang DTCTypeOfAssume = Assume + DTCTypeOfBase
  sem typeOfH env =
  | TmAssume r ->
    result.bind (typeOfH env r.dist) (lam dist.
      match dist with {ty = TyDist distr} then
        let c = dtcEnvMaxc (dtcEnvWeaken dist.fv env) in
        result.ok { dist with e = R (), ty = mulcType c distr.ty }
      else
        result.err
          (DTCArgError
            (Some (infoTm r.dist, (tydist_ (tyvar_ "a"), dist.ty)))))
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
      let ty = tyfloatc_ (M ()) in
      if subtype (weight.ty, ty) then
        result.ok {
          weight with e = R (), ty = tyWithInfo r.info tyunit_
        }
      else argErr r.weight weight.ty ty)
end

lang DTCTypeOfDist = Dist + DTCTypeOfBase
  sem typeOfH env =
  | TmDist r ->
    result.bind (mapAccumLTypeOfH env (distParams r.dist)) (lam t.
      match t with ((e, fv), tys) in
      match distTy r.info r.dist with ([], paramTys, suppTy) then
        let params = distParams r.dist in
        let paramTys = map fromMExprTy paramTys in
        let suppTy = fromMExprTy suppTy in
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
      else result.err (DTCPolyDistError (Some r.info)))
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
    let mod =
      switch
        optionGetOrElse
          (lam.
            error "found a diff without a modifier which should be impossible")
          r.mod
      case Analytic _ then A ()
      case PAP _ then P ()
      end
    in
    result.bind3
      -- NOTE(oerikss, 2025-03-13): For practical reasons the syntax of `diff`
      -- differs slightly compared to the formalization. In the implementation
      -- we provide the argument to the total derivative directly in the `diff`
      -- term. We do not need to promote `fn` because it is a function and
      -- `darg` because, regardless of its modifiers, we can always use T-Sub to
      -- lower modifiers to A.
      (typeOfH env r.fn) (typeOfHPromote env r.arg) (typeOfH env r.darg)
      (lam fn. lam arg. lam darg.
        match fn with {ty = TyArrowCE (arr & {e = D _})} then
          if and (eqcType mod arr.from) (isIsomorficToRn arr.to)
          then
            if subtype (arg.ty, arr.from) then
              if subtype (darg.ty, setC (A ()) arr.from) then
                resultOK [fn.e, arg.e] arr.to [fn.fv, arg.fv]
              else argErr r.darg darg.ty arr.from
            else argErr r.arg arg.ty arr.from
          else result.err (DTCDiffFnError (Some (infoTm r.fn, mod, fn.ty)))
        else result.err (DTCDiffFnError (Some (infoTm r.fn, mod, fn.ty))))
end

lang DTCTypeOfSolveODE = SolveODE + IsIsomorficToRn + DTCTypeOfBase
  sem typeOfH env =
  | TmSolveODE r ->
    result.bind4
      (sfold_ODESolverMetod_Expr
         (foldTypeOfH env)
         (result.ok { e = D (), fv = setEmpty nameCmp }) r.method)
      (typeOfH env r.model)
      (typeOfHPromote env r.init)
      (typeOfHPromote env r.endTime)
      (lam method. lam model. lam init. lam endTime.
        match model
          with
          {ty = TyArrowCE (arr1 & {
            from = TyFloatC _, to = TyArrowCE (arr2 & {e = D _}), e = D _})}
        then
          if allb [
            isIsomorficToRn arr2.from,
            isIsomorficToRn arr2.to
          ] then
            let ty =
              optionGetOrElse (lam. error "impossible")
                (meetType (arr2.from, arr2.to))
            in
            let modelTy =
              TyArrowCE { arr1 with to = tyarrowe_ ty ty (A ()) (D ()) }
            in
            if subtype (model.ty, modelTy) then
              if subtype (init.ty, ty) then
                -- let tys = (endTime.ty, tyfloatc_ (P ())) in
                if subtype (endTime.ty, tyfloatc_ (P ())) then
                  if subtype (endTime.ty, arr1.from) then
                    resultOK [method.e, model.e, init.e, endTime.e] ty
                      [method.fv, model.fv, init.fv, endTime.fv]
                  else argErr r.endTime endTime.ty (arr1.from)
                else argErr r.endTime endTime.ty (tyfloatc_ (P ()))
              else argErr r.init init.ty ty
            else argErr r.model model.ty modelTy
          else
            result.err
              (DTCSolveODEModelError (Some (infoTm r.model, model.ty)))
        else
          result.err
            (DTCSolveODEModelError (Some (infoTm r.model, model.ty))))
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
  use DTCAst in ityarrowe_ info from to (A ()) (D ())
let arr_ = lam from. lam to.
  use DTCAst in ityarrowe_ (NoInfo ()) from to (A ()) (D ())

lang DTCFloatType = DTCTyConst
  sem dtcConstType info =| CFloat _ -> result.ok (ityfloatc_ info (M ()))
end

lang DTCArithFloatType = ArithFloatAst + DTCTyConst
  sem dtcConstType info =
  | CAddf _ | CSubf _ | CMulf _ | CDivf _ ->
    let tyfloata = ityfloatc_ info (A ()) in
    let arr = lam from. lam to. iarr_ info from to in
    result.ok (arr tyfloata (arr tyfloata tyfloata))
  | CNegf _ ->
    let tyfloata = ityfloatc_ info (A ()) in
    result.ok (iarr_ info tyfloata tyfloata)
end

lang DTCElementaryFunctionsType = ElementaryFunctions + DTCTyConst
  sem dtcConstType info =
  | CSin _ | CCos _ | CSqrt _  | CExp _ | CLog _ ->
    let tyfloata = ityfloatc_ info (A ()) in
    result.ok (iarr_ info tyfloata tyfloata)
  | CPow _ ->
    let tyfloata = ityfloatc_ info (A ()) in
    let arr = lam from. lam to. iarr_ info from to in
    result.ok (arr tyfloata (arr tyfloata tyfloata))
end

lang DTCCmpFloatAstType = CmpFloatAst + DTCTyConst
  sem dtcConstType info =
  | CEqf _ | CLtf _ | CLeqf _ | CGtf _ | CGeqf _ | CNeqf _ ->
    let tyfloatp = ityfloatc_ info (P ()) in
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
    result.err (DTCArgError (Some (infoTm tm, (tyseq_ _a, ty))))

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
          ty = ityarrowe_ r.info (seq arr.from) (seq arr.to) (A ()) arr.e
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
                 (A ())
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
          ty = ityarrowe_ r.info (ityseq_ r.info arr.from) arr.to (A ()) arr.e
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
                   (A ())
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
            let arr = lam from. lam to. ityarrowe_ r.info from to (A ()) in
            result.ok {
              rhs with
              ty =
                arr
                  ty
                  (arr (ityseq_ r.info arr2.from) ty (dtcMule arr1.e arr2.e))
                  (D ())
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
            let arr = lam from. lam to. ityarrowe_ r.info from to (A ()) in
            result.ok {
              rhs with
              ty =
                arr
                  ty
                  (arr (ityseq_ r.info arr1.from) ty (dtcMule arr1.e arr2.e))
                  (D ())
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
    result.err (DTCArgError (Some (infoTm tm, (tydist_ _a, ty))))

  sem typeOfH env =
  | TmApp (r & {lhs = TmConst {val = CDistEmpiricalSamples _}}) ->
    result.bind (typeOfH env r.rhs) (lam rhs.
      match rhs with {ty = TyDist distr} then
        let seq = ityseq_ r.info in
        result.ok {
          rhs with ty = itytuple_ r.info [
            seq distr.ty, seq (ityfloatc_ r.info (M ()))]
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
        result.ok { rhs with ty = ityfloatc_ r.info (M ()) }
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
        optionMapOr (result.err (DTCJoinError (Some (r.info, (patTy, ty)))))
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
            Some (result.err (DTCPatError (Some (pr.info, TyRecord tr))))
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

-- Drop "module name" for brevity
let _D = D () in
let _R = R () in
let _A = A () in
let _P = P () in
let _M = M () in

-- Define some shorthand names. We order these to make testing easier.
let _x = nameNoSym "x" in
let _y = nameNoSym "y" in
let _z = nameNoSym "z" in
let _u = nameNoSym "u" in
let _v = nameNoSym "v" in
let _f = nameNoSym "f" in
let _g = nameNoSym "g" in
let _h = nameNoSym "h" in

let alltypes = [
  tyfloatc_ _A, tyfloatc_ _P, tyfloatc_ _M,
  tyarrowe_ (tyfloatc_ _A) (tyfloatc_ _A) _A _D,
  tyarrowe_ (tyfloatc_ _A) (tyfloatc_ _A) _A _R,
  tyarrowe_ (tyfloatc_ _A) (tyfloatc_ _A) _P _D,
  tyarrowe_ (tyfloatc_ _A) (tyfloatc_ _A) _P _R,
  tyarrowe_ (tyfloatc_ _A) (tyfloatc_ _A) _M _D,
  tyarrowe_ (tyfloatc_ _A) (tyfloatc_ _A) _M _R,
  tytuple_ [tyfloatc_ _A, tyfloatc_ _P, tyfloatc_ _M],
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
    (tyarrowe_
       (tyfloatc_ _A)
       (tyarrowe_ (tychar_) (tyfloatc_ _A) _A _D)
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
  tyarrowe_ (tyfloatc_ _A) (tyfloatc_ _A) _A _D
] in
utest leqcType _A rhs with false in
utest leqcType _P rhs with false in
utest leqcType _M rhs with true in

-- ┌──────────────┐
-- │ Test eqcType │
-- └──────────────┘

utest eqcType _A (tyfloatc_ _A) with true in
utest eqcType _A (tyfloatc_ _P) with false in
utest eqcType _P (tyfloatc_ _A) with false in
let rhs = tytuple_ [
  tyfloatc_ _P,
  tyseq_ (tyfloatc_ _M),
  tyarrowe_ (tyfloatc_ _A) (tyfloatc_ _A) _A _D
] in
utest eqcType _A rhs with false in
utest eqcType _P rhs with false in
utest eqcType _M rhs with false in
let rhs = lam c. tytuple_ [
  tyfloatc_ c,
  tyseq_ (tyfloatc_ c)
] in
utest eqcType _A (rhs _A) with true in
utest eqcType _P (rhs _A) with false in
utest eqcType _M (rhs _A) with false in
utest eqcType _A (rhs _P) with false in
utest eqcType _P (rhs _P) with true in
utest eqcType _M (rhs _P) with false in
let rhs = tytuple_ [
  tyfloatc_ _M,
  tyseq_ (tyfloatc_ _M),
  tyarrowe_ (tyfloatc_ _A) (tyfloatc_ _A) _M _D
] in
utest eqcType _A rhs with false in
utest eqcType _P rhs with false in
utest eqcType _M rhs with true in

-- ┌───────────────┐
-- │ Test leqTypec │
-- └───────────────┘

utest leqTypec (tyfloatc_ _A) _A with true in
utest leqTypec (tyfloatc_ _P) _A with true in
utest leqTypec (tyfloatc_ _A) _P with false in
let rhs = tytuple_ [
  tyfloatc_ _P,
  tyseq_ (tyfloatc_ _M),
  tyarrowe_ (tyfloatc_ _A) (tyfloatc_ _A) _P _D
] in
utest leqTypec rhs _A with true in
utest leqTypec rhs _P with true in
utest leqTypec rhs _M with false in

-- ┌─────────────────┐
-- │ Test dtcLeqcEnv │
-- └─────────────────┘

utest dtcLeqcEnv _A (dtcEnvOfSeq []) with true in
utest dtcLeqcEnv _A (dtcEnvOfSeq [(_x, tyfloatc_ _A)]) with true in
let env = dtcEnvOfSeq [(_x, tyfloatc_ _P), (_y, tyfloatc_ _M)] in
utest dtcLeqcEnv _A env with false in
utest dtcLeqcEnv _P env with false in
utest dtcLeqcEnv _M env with true in
utest
  dtcLeqcEnv _M
    (dtcEnvOfSeq [(_x, (tyarrowe_ (tychar_) (tyfloatc_ _A) _A _D))])
  with true
in

-- ┌───────────────┐
-- │ Test mulcType │
-- └───────────────┘

utest mulcType _A (tyfloatc_ _A) with tyfloatc_ _A using eqType in
utest mulcType _A (tyfloatc_ _P) with tyfloatc_ _P using eqType in
utest mulcType _P (tyfloatc_ _A) with tyfloatc_ _P using eqType in
utest mulcType _M (tyarrowe_ (tyfloatc_ _A) (tyfloatc_ _A) _A _D) with
  tyarrowe_ (tyfloatc_ _A) (tyfloatc_ _A) _M _D using eqType
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
utest _subtype _A _P with false in
utest _subtype _A _M with false in
utest _subtype _P _A with true in
utest _subtype _P _P with true in
utest _subtype _P _M with false in
utest _subtype _M _A with true in
utest _subtype _M _P with true in
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
  tyarrowe_ (tyfloatc_ c1) (tyfloatc_ c2) _A e
in

utest subtype (arr _A _A _D, arr _A _A _D) with true in
utest subtype (arr _A _A _D, arr _A _A _R) with true in
utest subtype (arr _A _A _R, arr _A _A _R) with true in
utest subtype (arr _A _A _R, arr _A _A _D) with false in
utest subtype (arr _A _P _D, arr _A _A _D) with true in
utest subtype (arr _A _A _D, arr _P _A _D) with true in

let arr = lam c.
  tyarrowe_ (tyfloatc_ _A) (tyfloatc_ _A) c _D
in

utest subtype (arr _A, arr _A) with true in
utest subtype (arr _P, arr _A) with true in
utest subtype (arr _M, arr _A) with true in
utest subtype (arr _A, arr _P) with false in
utest subtype (arr _P, arr _P) with true in
utest subtype (arr _M, arr _P) with true in
utest subtype (arr _A, arr _M) with false in
utest subtype (arr _P, arr _M) with false in
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

utest _joinType _A _A with Some (tyfloatc_ _A) using eq in
utest _joinType _A _P with Some (tyfloatc_ _A) using eq in
utest _joinType _P _A with Some (tyfloatc_ _A) using eq in
utest _joinType _A _M with Some (tyfloatc_ _A) using eq in
utest _joinType _M _A with Some (tyfloatc_ _A) using eq in
utest _joinType _P _P with Some (tyfloatc_ _P) using eq in
utest _joinType _M _P with Some (tyfloatc_ _P) using eq in
utest _joinType _P _M with Some (tyfloatc_ _P) using eq in
utest _joinType _M _M with Some (tyfloatc_ _M) using eq in

let _meetType = lam c1. lam c2. meetType (tyfloatc_ c1, tyfloatc_ c2) in

utest _meetType _A _A with Some (tyfloatc_ _A) using eq in
utest _meetType _A _P with Some (tyfloatc_ _P) using eq in
utest _meetType _P _A with Some (tyfloatc_ _P) using eq in
utest _meetType _A _M with Some (tyfloatc_ _M) using eq in
utest _meetType _M _A with Some (tyfloatc_ _M) using eq in
utest _meetType _P _P with Some (tyfloatc_ _P) using eq in
utest _meetType _M _P with Some (tyfloatc_ _M) using eq in
utest _meetType _P _M with Some (tyfloatc_ _M) using eq in
utest _meetType _M _M with Some (tyfloatc_ _M) using eq in

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
let arr = tyarrowe_ (tyfloatc_ _A) (tyfloatc_ _A) _A in
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

let arr = lam c. tyarrowe_ (tyfloatc_ c) (tyfloatc_ _A) _A _D in
let _joinType = lam c1. lam c2. joinType (arr c1, arr c2) in

utest _joinType _A _P with Some (arr _P) using eq in
utest _joinType _P _A with Some (arr _P) using eq in
utest _joinType _A _M with Some (arr _M) using eq in
utest _joinType _M _A with Some (arr _M) using eq in
utest _joinType _P _M with Some (arr _M) using eq in
utest _joinType _M _P with Some (arr _M) using eq in
utest _joinType _P _P with Some (arr _P) using eq in
utest _joinType _M _M with Some (arr _M) using eq in

let _meetType = lam c1. lam c2. meetType (arr c1, arr c2) in

utest _meetType _A _P with Some (arr _A) using eq in
utest _meetType _P _A with Some (arr _A) using eq in
utest _meetType _A _M with Some (arr _A) using eq in
utest _meetType _M _A with Some (arr _A) using eq in
utest _meetType _P _M with Some (arr _P) using eq in
utest _meetType _M _P with Some (arr _P) using eq in
utest _meetType _P _P with Some (arr _P) using eq in
utest _meetType _M _M with Some (arr _M) using eq in

let arr = lam c. tyarrowe_ (tyfloatc_ _A) (tyfloatc_ c) _A _D in
let _joinType = lam c1. lam c2. joinType (arr c1, arr c2) in

utest _joinType _A _P with Some (arr _A) using eq in
utest _joinType _P _A with Some (arr _A) using eq in
utest _joinType _A _M with Some (arr _A) using eq in
utest _joinType _M _A with Some (arr _A) using eq in
utest _joinType _P _M with Some (arr _P) using eq in
utest _joinType _M _P with Some (arr _P) using eq in
utest _joinType _P _P with Some (arr _P) using eq in
utest _joinType _M _M with Some (arr _M) using eq in

let _meetType = lam c1. lam c2. meetType (arr c1, arr c2) in

utest _meetType _A _P with Some (arr _P) using eq in
utest _meetType _P _A with Some (arr _P) using eq in
utest _meetType _A _M with Some (arr _M) using eq in
utest _meetType _M _A with Some (arr _M) using eq in
utest _meetType _P _M with Some (arr _M) using eq in
utest _meetType _M _P with Some (arr _M) using eq in
utest _meetType _P _P with Some (arr _P) using eq in
utest _meetType _M _M with Some (arr _M) using eq in

let arr = lam c. tyarrowe_ (tyfloatc_ _A) (tyfloatc_ _A) c _D in
let _joinType = lam c1. lam c2. joinType (arr c1, arr c2) in

utest _joinType _A _A with Some (arr _A) using eq in
utest _joinType _A _P with Some (arr _A) using eq in
utest _joinType _P _A with Some (arr _A) using eq in
utest _joinType _A _M with Some (arr _A) using eq in
utest _joinType _M _A with Some (arr _A) using eq in
utest _joinType _P _P with Some (arr _P) using eq in
utest _joinType _P _M with Some (arr _P) using eq in
utest _joinType _M _P with Some (arr _P) using eq in
utest _joinType _M _M with Some (arr _M) using eq in

let _meetType = lam c1. lam c2. meetType (arr c1, arr c2) in

utest _meetType _A _A with Some (arr _A) using eq in
utest _meetType _A _P with Some (arr _P) using eq in
utest _meetType _P _A with Some (arr _P) using eq in
utest _meetType _A _M with Some (arr _M) using eq in
utest _meetType _M _A with Some (arr _M) using eq in
utest _meetType _P _P with Some (arr _P) using eq in
utest _meetType _P _M with Some (arr _M) using eq in
utest _meetType _M _P with Some (arr _M) using eq in
utest _meetType _M _M with Some (arr _M) using eq in

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
utest joinType (dist _P, dist _P) with Some (dist _P) using eq in
utest meetType (dist _A, dist _A) with Some (dist _A) using eq in
utest meetType (dist _A, dist _P) with Some (dist _P) using eq in
utest meetType (dist _P, dist _A) with Some (dist _P) using eq in
utest meetType (dist _P, dist _P) with Some (dist _P) using eq in

-- ┌───────────────┐
-- │ Test mincType │
-- └───────────────┘

-- Bottom
utest mincType tybot_ with _A in

-- Float
let _mincType = lam c. mincType (tyfloatc_ c) in

utest _mincType _A with _A in
utest _mincType _P with _P in
utest _mincType _M with _M in

-- Seqences
let _mincType = lam c. mincType (tyseq_ (tyfloatc_ c)) in

utest _mincType _A with _A in
utest _mincType _P with _P in
utest _mincType _M with _M in

-- Records
let _mincType = lam c1. lam c2. mincType (tytuple_ [tyfloatc_ c1, tyfloatc_ c2]) in

utest _mincType _A _A with _A in
utest _mincType _A _P with _P in
utest _mincType _A _M with _M in
utest _mincType _P _A with _P in
utest _mincType _P _P with _P in
utest _mincType _P _M with _M in
utest _mincType _M _A with _M in
utest _mincType _M _P with _M in
utest _mincType _M _M with _M in

-- Arrows
let _mincType = lam c1. lam c2.
  mincType (tyarrowe_ (tyfloatc_ c1) (tyfloatc_ c2) _A _D)
in

utest _mincType _A _A with _A in
utest _mincType _A _P with _A in
utest _mincType _A _M with _A in
utest _mincType _P _A with _A in
utest _mincType _P _P with _A in
utest _mincType _P _M with _A in
utest _mincType _M _A with _A in
utest _mincType _M _P with _A in
utest _mincType _M _M with _A in

-- Type variables
utest mincType (tyvar_ "X") with _A in

-- Distributions
let _mincType = lam c. mincType (tydist_ (tyfloatc_ c)) in

utest _mincType _A with _A in
utest _mincType _P with _A in
utest _mincType _M with _A in

-- ┌────────────────────────────┐
-- │ Test dtcEnvMinc/dtcEnvMaxc │
-- └────────────────────────────┘

let genC = lam.
  switch randIntU 0 2
  case 0 then A ()
  case 1 then P ()
  case 2 then M ()
  end
in

let genEnv = lam.
  dtcEnvOfSeq [
    (_x, tyfloatc_ (genC ())),
    (_y, tyfloatc_ (genC ())),
    (_z, tyfloatc_ (genC ())),
    (_f, tyarrowe_ (tyfloatc_ _A) (tyfloatc_ _A) (genC ()) _D),
    (_g, tydist_ (tyfloatc_ _A))
  ]
in

repeat
  (lam. let env = genEnv () in
      let minc = dtcEnvMinc env in
      let maxc = dtcEnvMaxc env in
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
      let allcs = [A (), P (), M ()] in
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
let arrce = lam ps. lam ret. foldr (lam t. lam to. tyarrowe_ t.0 to t.1 t.2) ret ps in
let arr = lam ps. arrce (map (lam p. (p, _A, _D)) ps) in
let arrc = lam ps. arrce (map (lam p. (p.0, p.1, _D)) ps) in
let arre = lam ps. arrce (map (lam p. (p.0, _A, p.1)) ps) in
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

-- Basic tests
utest _typeOf [] (lam_ [(_x, tyint_)] x)
  with Right (_D, arrc [(tyint_, _M)] tyint_)
  using eq else onFail
in

utest _typeOf [(_x, tyint_)] (app_ x x)
  with Left [DTCArrowError (None ())]
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
  with Left [DTCArgError (None ())]
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
  with Left [DTCArgError (None ())]
  using eq else onFail
in

utest
  _typeOf env (f [g [f [x, y], x], y])
  with Left [DTCArgError (None ())]
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
  with Left [DTCArgError (None ())]
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
  with Right (_D, arrce [(flt _P, _P, _R), (flt _M, _A, _D)] (flt _A))
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
  with Left [DTCPatError (None ())]
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
  with Left [DTCPatError (None ())]
  using eq else onFail
in

utest
  _typeOf [(_x, tybool_)] (match_ x (pchar_ '0') x x)
  with Left [DTCPatError (None ())]
  using eq else onFail
in

utest
  _typeOf [(_x, tyint_)] (match_ x ptrue_ x x)
  with Left [DTCPatError (None ())]
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
  with Left [DTCPatError (None ())]
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
  with Left [DTCArgError (None ())]
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
  with Left [DTCArgError (None ())]
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
  with Left [DTCArgError (None ())]
  using eq else onFail
in

-- Observe

utest _typeOf [(_x, tydist_ (flt _A))] (observe_ (float_ 0.) x)
  with Right (_D, tyunit_)
  using eq else onFail
in

utest _typeOf [(_x, tydist_ (flt _A))] (observe_ (int_ 0) x)
  with Left [DTCArgError (None ())]
  using eq else onFail
in

utest _typeOf [(_x, flt _A)] (observe_ (float_ 0.) x)
  with Left [DTCArgError (None ())]
  using eq else onFail
in

-- Weight

utest _typeOf [(_x, flt _A)] (weight_ x)
  with Left [DTCArgError (None ())]
  using eq else onFail
in

utest _typeOf [(_x, flt _P)] (weight_ x)
  with Left [DTCArgError (None ())]
  using eq else onFail
in

utest _typeOf [(_x, flt _M)] (weight_ x)
  with Right (_R, tyunit_)
  using eq else onFail
in

utest _typeOf [] (weight_ (int_ 0))
  with Left [DTCArgError (None ())]
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
  with Right (_D, tydist_ (arr [flt _M] (flt _M)))
  using eq else onFail
in

utest _typeOf [(_x, flt _M)] (dist_ (DExponential {rate = x}))
  with Right (_D, tydist_ (flt _M))
  using eq else onFail
in

utest _typeOf [(_x, (tyseq_ (tytuple_ [flt _M, flt _M])))]
        (dist_ (DEmpirical {samples = x}))
  with Left [DTCPolyDistError (None ())]
  using eq else onFail
in

let _test = lam c.
  _typeOf [(_x, flt c)] (dist_ (DExponential {rate = x}))
in

utest _test _A
  with Left [DTCArgError (None ())]
  using eq else onFail
in

utest _test _P
  with Left [DTCArgError (None ())]
  using eq else onFail
in

-- Diff

let _test = lam mod. lam c1. lam c2. lam c3. lam c4. lam e. _typeOf [
  (_x, arre [(flt c1, e)] (flt c2)),
  (_y, flt c3),
  (_z, flt c4)
] (TmDiff {
  fn = x,
  arg = y,
  darg = z,
  mod = Some mod,
  ty = tyunknown_,
  info = NoInfo ()
}) in

utest
  _test (Analytic ()) _A _A _A _A _D
  with Right (_D, flt _A)
  using eq else onFail
in

utest
  _test (Analytic ()) _A _A _P _P _D
  with Right (_D, flt _A)
  using eq else onFail
in

utest
  _test (Analytic ()) _A _A _M _M _D
  with Right (_D, flt _A)
  using eq else onFail
in

utest
  _test (Analytic ()) _A _P _A _A _D
  with Right (_D, flt _P)
  using eq else onFail
in

utest
  _test (Analytic ()) _A _M _A _A _D
  with Right (_D, flt _M)
  using eq else onFail
in

utest
  _test (Analytic ()) _P _A _A _A _D
  with Left [DTCDiffFnError (None ())]
  using eq else onFail
in

utest
  _test (Analytic ()) _M _A _A _A _D
  with Left [DTCDiffFnError (None ())]
  using eq else onFail
in

utest
  _test (Analytic ()) _A _A _A _A _R
  with Left [DTCDiffFnError (None ())]
  using eq else onFail
in

utest
  _test (PAP ()) _A _A _A _A _D
  with Left [DTCDiffFnError (None ())]
  using eq else onFail
in

utest
  _test (PAP ()) _P _A _A _A _D
  with Left [DTCArgError (None ())]
  using eq else onFail
in

utest
  _test (PAP ()) _P _A _P _A _D
  with Right (_D, flt _A)
  using eq else onFail
in

utest
  _test (PAP ()) _P _A _M _A _D
  with Right (_D, flt _A)
  using eq else onFail
in

utest
  _test (PAP ()) _M _A _P _A _D
  with Left [DTCDiffFnError (None ())]
  using eq else onFail
in

utest
  _test (PAP ()) _M _A _M _A _D
  with Left [DTCDiffFnError (None ())]
  using eq else onFail
in

utest
  _typeOf [
    (_x, arr [tyseq_ (tytuple_ [flt _A, tyint_])] (flt _A)),
    (_y, (tyseq_ (tytuple_ [flt _A, tyint_]))),
    (_z, (tyseq_ (tytuple_ [flt _A, tyint_])))
  ] (diffp_ x y z)
  with Left [DTCDiffFnError (None ())]
  using eq else onFail
in

utest
  _typeOf [
    (_x, arr [flt _A] (tyseq_ (tytuple_ [flt _A, tyint_]))),
    (_y, (flt _A)),
    (_z, (flt _A))
  ] (diffp_ x y z)
  with Left [DTCDiffFnError (None ())]
  using eq else onFail
in

-- Solve

utest
  _typeOf [
    (_x, arr [flt _A, tytuple_ [flt _A, flt _A]] (tytuple_ [flt _A, flt _A])),
    (_y, tytuple_ [flt _A, flt _A]),
    (_z, flt _P)
  ] (solveode_ x y z)
  with Right (_D, tytuple_ [flt _A, flt _A])
  using eq else onFail
in

let _test = lam c.
  _typeOf [
    (_x, arr [flt _A, flt _P] (flt c)),
    (_y, flt c),
    (_z, flt _P)
  ] (solveode_ x y z)
in

utest
  _test _A
  with Left [DTCArgError (None ())]
  using eq else onFail
in

utest
  _test _P
  with Right (_D, flt _P)
  using eq else onFail
in

utest
  _test _M
  with Right (_D, flt _M)
  using eq else onFail
in

let _test = lam c.
  _typeOf [
    (_x, arr [flt _A, flt _A] (flt _A)),
    (_y, flt _A),
    (_z, flt c)
  ] (solveode_ x y z)
in

utest
  _test _A
  with Left [DTCArgError (None ())]
  using eq else onFail
in

utest
  _test _P
  with Right (_D, flt _A)
  using eq else onFail
in

utest
  _test _M
  with Right (_D, flt _A)
  using eq else onFail
in

let _test = lam c.
  _typeOf [
    (_x, arr [flt _A, flt _P] (flt _P)),
    (_y, flt c),
    (_z, flt _P)
  ] (solveode_ x y z)
in

utest
  _test _A
  with Left [DTCArgError (None ())]
  using eq else onFail
in

utest
  _test _P
  with Right (_D, flt _P)
  using eq else onFail
in

utest
  _test _M
  with Right (_D, flt _P)
  using eq else onFail
in

-- NOTE(oerikss, 2024-10-23): This would otherwise allow us to construct
-- an unsafe coerce term:
-- `id = lam z : FloatA. solve (lam FloatA. lam : FloatA. 0.) z 0.` where
-- `id t` coerces any term `t : FloatA` to `FloatN`.
utest
  _typeOf [
    (_x, arr [flt _A, flt _A] (flt _M)),
    (_y, flt _A),
    (_z, flt _P)
  ] (solveode_ x y z)
  with Left [DTCArgError (None ())]
  using eq else onFail
in

let env =  [
  (_x, arr [flt _A, flt _P] (flt _P)),
  (_y, flt _P),
  (_z, flt _P)
] in

utest
  _typeOf
    (concat env [(_u, arr [flt _M] (flt _M)), (_v, flt _A)])
    (solveodeWithStepSize_ (app_ u v) x y z)
  with Left [DTCArgError (None ())]
  using eq else onFail
in

utest
  _typeOf
    (concat env [(_u, arre [(flt _A, _R)] (flt _M)), (_v, flt _A)])
    (solveodeWithStepSize_ (app_ u v) x y z)
  with Right (_R, flt _P)
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
  with Right (_D, _ty _A _A _A)
  using eq else onFail
in

utest _typeOf env (_tm _P)
  with Right (_D, (_ty _P _P _P))
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
  with Right (_D, _ty _A _A _A)
  using eq else onFail
in

utest _typeOf env (_tm _M z (float_ 0.))
  with Right (_D, _ty _M _M _M)
  using eq else onFail
in

utest _typeOf env (_tm _A z (float_ 0.))
  with Left [DTCArgError (None ())]
  using eq else onFail
in

-- Example 2

let _tm = lam c. nlam_ _x (flt c) (if_ (gtf_ x (float_ 0.)) x (negf_ x)) in

utest _typeOf [] (_tm _A)
  with Left [DTCArgError (None ())]
  using eq else onFail
in

utest _typeOf [] (_tm _P)
  with Right (_D, arrc [(flt _P, _P)] (flt _P))
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
  with Left [DTCContextConstraintError (None ())]
  using eq else onFail
in

utest
  _typeOf []
    (nlam_ _x (flt _P)
       (mulf_ x (expectation_ (infer__ (nlam_ _y tyunit_ (float_ 1.))))))
  with Right (_D, arrc [(flt _P, _P)] (flt _P))
  using eq else onFail
in

()
