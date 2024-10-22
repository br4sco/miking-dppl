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

-- Effects are either deterministic (det) or random (rnd)
type DTCEffect
con Det : () -> DTCEffect
con Rnd : () -> DTCEffect

let dtcEffectToString : DTCEffect -> String = lam e.
  switch e
  case Det _ then "det"
  case Rnd _ then "rnd"
  end

-- Orders effects which are ordered det < rnd
let dtcLeqe : DTCEffect -> DTCEffect -> Bool
  = lam a. lam b.
    switch (a, b)
    case (Det _, _) then true
    case (_, Det _) then false
    case (Rnd _, _) then true
    case (_, Rnd _) then false
    end

utest dtcLeqe (Det ()) (Det ()) with true
utest dtcLeqe (Det ()) (Rnd ()) with true
utest dtcLeqe (Rnd ()) (Det ()) with false
utest dtcLeqe (Rnd ()) (Rnd ()) with true

-- Multiplication over effects
let dtcMule : DTCEffect -> DTCEffect -> DTCEffect
  = lam a. lam b.
    switch (a, b)
    case (Det _, _) then b
    case (_, Det _) then a
    case (Rnd _, _) then a
    case (_, Rnd _) then b
    end

utest dtcMule (Det ()) (Det ()) with (Det ())
utest dtcMule (Det ()) (Rnd ()) with (Rnd ())
utest dtcMule (Rnd ()) (Det ()) with (Rnd ())
utest dtcMule (Rnd ()) (Rnd ()) with (Rnd ())

-- Equality over effects
let dtcEqe : DTCEffect -> DTCEffect -> Bool
  = lam a. lam b.
    switch (a, b)
    case (Det _, Det _) | (Rnd _, Rnd _) then true
    case _ then false
    end

utest dtcEqe (Det ()) (Det ()) with true
utest dtcEqe (Det ()) (Rnd ()) with false
utest dtcEqe (Rnd ()) (Det ()) with false
utest dtcEqe (Rnd ()) (Rnd ()) with true

-- Coeffects are either analytic (A), piecewise analytic under analytic
-- partitioning (P), or non-differential (N).
type DTCCoeffect
con A : () -> DTCCoeffect
con P : () -> DTCCoeffect
con N : () -> DTCCoeffect

let dtcCoeffectToString : DTCCoeffect -> String = lam e.
  switch e
  case A _ then "A"
  case P _ then "P"
  case N _ then "N"
  end

-- Orders coeffects which are ordered A < P < N
let dtcLeqc : DTCCoeffect -> DTCCoeffect -> Bool
  = lam a. lam b.
    switch (a, b)
    case (A _, _) then true
    case (_, A _) then false
    case (P _, _) then true
    case (_, P _) then false
    case (N _, _) then true
    case (_, N _) then false
    end

utest dtcLeqc (A ()) (A ()) with true
utest dtcLeqc (A ()) (P ()) with true
utest dtcLeqc (A ()) (N ()) with true
utest dtcLeqc (P ()) (A ()) with false
utest dtcLeqc (P ()) (P ()) with true
utest dtcLeqc (P ()) (N ()) with true
utest dtcLeqc (N ()) (A ()) with false
utest dtcLeqc (N ()) (P ()) with false
utest dtcLeqc (N ()) (N ()) with true

-- Equality over coeffects
let dtcEqc : DTCCoeffect -> DTCCoeffect -> Bool
  = lam a. lam b.
    switch (a, b)
    case (A _, A _) | (P _, P _) | (N _, N _) then true
    case _ then false
    end

utest dtcEqc (A ()) (A ()) with true
utest dtcEqc (A ()) (P ()) with false
utest dtcEqc (A ()) (N ()) with false
utest dtcEqc (P ()) (A ()) with false
utest dtcEqc (P ()) (P ()) with true
utest dtcEqc (P ()) (N ()) with false
utest dtcEqc (N ()) (A ()) with false
utest dtcEqc (N ()) (P ()) with false
utest dtcEqc (N ()) (N ()) with true

-- Multiplication over coeffects
let dtcMulc : DTCCoeffect -> DTCCoeffect -> DTCCoeffect
  = lam a. lam b.
    switch (a, b)
    case (A _, _) then b
    case (_, A _) then a
    case (P _, _) then b
    case (_, P _) then a
    case (N _, _) then b
    case (_, N _) then a
    end

utest dtcMulc (A ()) (A ()) with (A ())
utest dtcMulc (A ()) (P ()) with (P ())
utest dtcMulc (A ()) (N ()) with (N ())
utest dtcMulc (P ()) (A ()) with (P ())
utest dtcMulc (P ()) (P ()) with (P ())
utest dtcMulc (P ()) (N ()) with (N ())
utest dtcMulc (N ()) (A ()) with (N ())
utest dtcMulc (N ()) (P ()) with (N ())
utest dtcMulc (N ()) (N ()) with (N ())

-- Min over coeffects
let dtcMinc : DTCCoeffect -> DTCCoeffect -> DTCCoeffect
  = lam a. lam b.
    switch (a, b)
    case (A _, _) then a
    case (_, A _) then b
    case (P _, _) then a
    case (_, P _) then b
    case (N _, _) then a
    case (_, N _) then b
    end

utest dtcMinc (A ()) (A ()) with (A ())
utest dtcMinc (A ()) (P ()) with (A ())
utest dtcMinc (A ()) (N ()) with (A ())
utest dtcMinc (P ()) (A ()) with (A ())
utest dtcMinc (P ()) (P ()) with (P ())
utest dtcMinc (P ()) (N ()) with (P ())
utest dtcMinc (N ()) (A ()) with (A ())
utest dtcMinc (N ()) (P ()) with (P ())
utest dtcMinc (N ()) (N ()) with (N ())

-- Max over coeffects
let dtcMaxc : DTCCoeffect -> DTCCoeffect -> DTCCoeffect
  = lam a. lam b.
    switch (a, b)
    case (A _, _) then b
    case (_, A _) then a
    case (P _, _) then b
    case (_, P _) then a
    case (N _, _) then b
    case (_, N _) then a
    end

utest dtcMaxc (A ()) (A ()) with (A ())
utest dtcMaxc (A ()) (P ()) with (P ())
utest dtcMaxc (A ()) (N ()) with (N ())
utest dtcMaxc (P ()) (A ()) with (P ())
utest dtcMaxc (P ()) (P ()) with (P ())
utest dtcMaxc (P ()) (N ()) with (N ())
utest dtcMaxc (N ()) (A ()) with (N ())
utest dtcMaxc (N ()) (P ()) with (N ())
utest dtcMaxc (N ()) (N ()) with (N ())

-- ┌───────────────┐
-- │ Annotated AST │
-- └───────────────┘

lang DTCAstBase = Ast + Eq
  -- NOTE(oerikss, 2024-10-07): The semantic functions in this fragment assumes
  -- that types and terms have been symbolized. I.e., it relies on unique
  -- identifiers in types and terms.

  -- `dtcLeqc` overloaded to types
  sem leqcType : DTCCoeffect -> Type -> Bool
  sem leqcType c =| ty -> true

  -- Scalar multiplication of coeffects over types
  sem mulcType : DTCCoeffect -> Type -> Type
  sem mulcType c =| ty -> ty

  -- Maximum coeffect `c` s.t. `leqcType c ty` is `true.
  sem maxcType : Type -> DTCCoeffect
  sem maxcType =| _ -> N ()

  -- Drops decorations from types
  sem eraseDecorations : Type -> Type
  sem eraseDecorations =| ty -> smap_Type_Type eraseDecorations ty

  sem eraseDecorationsFromTerm : Expr -> Expr
  sem eraseDecorationsFromTerm =| tm ->
    smap_Expr_Expr eraseDecorationsFromTerm (smap_Expr_Type eraseDecorations tm)

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

  -- Minimum coeffect modifier of type.
  sem mincType : Type -> DTCCoeffect
  sem mincType =| _ -> N ()

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
  sem eraseDecorations =
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
  | TyFloatC (r & {c = P ()}) -> (env, "Float")
  | TyFloatC (r & {c = N ()}) -> (env, "FloatN")

  -- Builder
  sem tyfloatc_ : DTCCoeffect -> Type
  sem tyfloatc_ =| c -> TyFloatC { info = NoInfo (), c = c }

  sem ityfloatc_ : Info -> DTCCoeffect -> Type
  sem ityfloatc_ info =| c -> TyFloatC { info = info, c = c }

  -- Conversions
  sem eraseDecorations =
  | TyFloatC r -> TyFloat { info = r.info }

  sem fromMExprTy =
  | TyFloat r -> ityfloatc_ r.info (N ())

  -- Coeffect/Type operations
  sem leqcType c =
  | TyFloatC r -> dtcLeqc c r.c

  sem mulcType c =
  | TyFloatC r -> TyFloatC { r with c = dtcMulc c r.c }

  sem maxcType =
  | TyFloatC r -> r.c

  sem subtype =
  | (TyFloatC l, TyFloatC r) -> dtcLeqc r.c l.c

  sem joinType =
  | (TyFloatC l, TyFloatC r) ->
    Some (if dtcLeqc l.c r.c then TyFloatC l else TyFloatC r)

  sem meetType =
  | (TyFloatC l, TyFloatC r) ->
    Some (if dtcLeqc l.c r.c then TyFloatC r else TyFloatC l)

  sem mincType =
  | TyFloatC r -> r.c

  sem setC : DTCCoeffect -> Type -> Type
  sem setC c =
  | TyFloatC r -> TyFloatC { r with c = c }
  | ty -> smap_Type_Type (setC c) ty
end

lang DTCFunTypeAst = DTCAstBase + FunTypeAst + PrettyPrint
  -- Arrow types are annotated with effects
  syn Type =| TyArrowE {info : Info, from : Type, to : Type, e : DTCEffect}

  -- Setters/Getters
  sem tyWithInfo info =| TyArrowE r -> TyArrowE {r with info = info}
  sem infoTy =| TyArrowE r -> r.info

  -- Shallow map/fold
  sem smapAccumL_Type_Type f acc =
  | TyArrowE r ->
    match f acc r.from with (acc, from) in
    match f acc r.to with (acc, to) in
    (acc, TyArrowE {r with from = from, to = to})

  -- Eq
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyArrowE r ->
    match unwrapType lhs with TyArrowE l then
      match eqTypeH typeEnv free l.from r.from with Some free then
        if dtcEqe l.e r.e then eqTypeH typeEnv free l.to r.to
        else None ()
      else None ()
    else None ()

  -- Pprint
  sem typePrecedence =
  | TyArrowE _ -> 0

  sem getTypeStringCode (indent : Int) (env: PprintEnv) =
  | TyArrowE r ->
    match printTypeParen indent 1 env r.from with (env, from) in
    match getTypeStringCode indent env r.to with (env, to) in
    match r.e with Rnd _ then (env, join [from, " -> (Rnd ", to, ")"])
    else (env, join [from, " -> ", to])

  -- Builder
  sem tyarrowe_ : Type -> Type -> DTCEffect -> Type
  sem tyarrowe_ from to =| e ->
    TyArrowE { info = NoInfo (), from = from, to = to, e = e }

  sem ityarrowe_ : Info -> Type -> Type -> DTCEffect -> Type
  sem ityarrowe_ info from to =| e ->
    TyArrowE { info = info, from = from, to = to, e = e }

  -- Conversions
  sem eraseDecorations =
  | TyArrowE r ->
    smap_Type_Type eraseDecorations
      (TyArrow { info = r.info, from = r.from, to = r.to })

  sem fromMExprTy =
  | TyArrow r ->
    smap_Type_Type fromMExprTy (ityarrowe_ r.info r.from r.to (Det ()))

  -- Coeffect/Type operations
  sem subtype c =
  | (TyArrowE l, TyArrowE r) ->
    allb [
      subtype (r.from, l.from),
      subtype (l.to, r.to),
      dtcLeqe l.e r.e
    ]

  sem joinType =
  | (TyArrowE l, TyArrowE r) ->
    optionBind (meetType (l.from, r.from)) (lam from.
      optionBind (joinType (l.to, r.to)) (lam to.
        Some
          (TyArrowE
            (if dtcLeqe l.e r.e then { r with from = from, to = to }
             else { l with from = from, to = to }))))

  sem meetType =
  | (TyArrowE l, TyArrowE r) ->
    optionBind (joinType (l.from, r.from)) (lam from.
      optionBind (meetType (l.to, r.to)) (lam to.
        Some
          (TyArrowE
            (if dtcLeqe l.e r.e then { l with from = from, to = to }
             else { r with from = from, to = to }))))
end

lang DTCSeqTypeAst = DTCAstBase + SeqTypeAst
  sem leqcType c =
  | ty & TySeq _ ->
    sfold_Type_Type (lam b. lam ty. and b (leqcType c ty)) true ty

  sem mulcType c =
  | ty & TySeq _ -> smap_Type_Type (mulcType c) ty

  sem maxcType =
  | ty & TySeq _ ->
    sfold_Type_Type (lam c. lam ty. dtcMaxc c (maxcType ty)) (A ()) ty

  sem subtype =
  | (TySeq l, TySeq r) -> subtype (l.ty, r.ty)

  sem _dtcSeqJoinMeet f l =| r ->
    optionMap (lam ty. TySeq { l with ty = ty }) (f (l.ty, r.ty))

  sem joinType =
  | (TySeq l, TySeq r) -> _dtcSeqJoinMeet joinType l r

  sem meetType =
  | (TySeq l, TySeq r) -> _dtcSeqJoinMeet meetType l r

  sem mincType =
  | TySeq r -> mincType r.ty
end

lang DTCRecordTypeAst = DTCAstBase + RecordTypeAst
  sem leqcType c =
  | ty & TyRecord _ ->
    sfold_Type_Type (lam b. lam ty. and b (leqcType c ty)) true ty

  sem mulcType c =
  | ty & TyRecord _ -> smap_Type_Type (mulcType c) ty

  sem maxcType =
  | ty & TyRecord _ ->
    sfold_Type_Type (lam c. lam ty. dtcMaxc c (maxcType ty)) (A ()) ty

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

  sem mincType =
  | ty & (TyRecord _) ->
    sfold_Type_Type (lam c. lam ty. dtcMinc c (mincType ty)) (N ()) ty
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

lang DTCEnv = DTCAst
  -- Fragment defining and implementing DPPL type environment

  type DTCEnv = Map Name Type

  -- Basic creation/accessing/manipulation/conversion.
  sem dtcEnvOfSeq : [(Name, Type)] -> DTCEnv
  sem dtcEnvOfSeq =| seq -> mapFromSeq nameCmp seq

  sem dtcEnvToSeq : DTCEnv -> [(Name, Type)]
  sem dtcEnvToSeq =| env -> mapToSeq env

  -- `dtcLeqc` overloaded to type environments.
  sem dtcLeqcEnv : DTCCoeffect -> DTCEnv -> Bool
  sem dtcLeqcEnv c =| env -> mapAll (leqcType c) env

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
  -- maximum coeffect modifier `c` s.t. `dtcLeqcEnv c env` is `true`.
  sem dtcEnvMinc : DTCEnv -> DTCCoeffect
  sem dtcEnvMinc =| env ->
    mapFoldWithKey (lam c. lam. lam ty. dtcMinc c (mincType ty)) (N ()) env
end


-- ┌──────────────┐
-- │ Type Checker │
-- └──────────────┘

lang DTCTypeError = Ast + PrettyPrint
  syn DTCTypeError =
  -- NOTE(oerikss, 2024-10-08): The error parameters are optional to make
  -- testing errors easier.
  | DTCArrowError (Option (Info, Type))
  | DTCParameterError (Option (Info, (Type, Type)))
  | DTCJoinError (Option (Info, (Type, Type)))
  | DTCPatError (Option (Info, Type))
  | DTCAnotError (Option Info)
  | DTCSolveODEModelError (Option (Info, Type))
  | DTCDiffFnError (Option (Info, Type))
  | DTCPolyDistError (Option Info)
  | DTCPolyConstError (Option Info)
  | DTCUnuspportedTermError (Option Info)

  sem typeErrorToMsg : DTCTypeError -> (Info, String)
  sem typeErrorToMsg =
  | DTCArrowError (Some (info, ty)) ->
    (info, _typeErrorToMsg2 ["Function type"] [type2str ty])
  | DTCParameterError (Some (info, (expected, found))) ->
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
       ["Function type Float(A|N) -> T -> T,",
        "where T isomorfic to (Float(A|N),...,Float(A|N))"]
       [type2str ty])
  | DTCDiffFnError (Some (info, ty)) ->
    (info,
     _typeErrorToMsg2
       ["Function type T -> T,",
        "where T isomorfic to (Float(A),...,Float(A))"]
       [type2str ty])
  | DTCPolyDistError (Some info) ->
    (info, "* Polymorfic distributions are currently not supported")
  | DTCPolyConstError (Some info) ->
    (info, join [
      "* Cannot infer the type of this polymorphic intrinsic.\n",
      "* Try to apply it to one or more argument."
    ])
  | DTCUnuspportedTermError (Some info) ->
    (info, "* This term is currently not supported")
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

  sem typeOfH : DTCEnv -> Expr -> Result DTCTypeError DTCTypeError ResultOk
  sem typeOfH env =| tm ->
    result.err (DTCUnuspportedTermError (Some (infoTm tm)))

  sem typeOfHPromote
    : DTCEnv -> Expr -> Result DTCTypeError DTCTypeError ResultOk
  sem typeOfHPromote env =| tm ->
    result.bind (typeOfH env tm) (lam tm.
      let c = dtcEnvMinc (dtcEnvWeaken tm.fv env) in
      result.ok { tm with ty = mulcType c tm.ty })

  sem resultOK
    : [DTCEffect] -> Type -> [Set Name]
      -> Result DTCTypeError DTCTypeError ResultOk
  sem resultOK es ty =| fvs ->
    result.ok { e = foldr1 dtcMule es, ty = ty, fv = foldr1 setUnion fvs }

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
             ((dtcMule e r.e, setUnion fv r.fv),
              mulcType (dtcEnvMinc (dtcEnvWeaken r.fv env)) r.ty))
           (Det (), setEmpty nameCmp)
           rs))
end

lang DTCTypeOfVar = VarAst + DTCTypeOfBase
  sem typeOfH env =
  | TmVar r ->
    result.ok {
      e = Det (),
      ty = optionGetOrElse (lam.
        error (strJoin " " [
          "typeOf: Illformed type environment.",
          "This should not happen when type-checking a symbolized term."]))
             (dtcEnvLookup r.ident env),
      fv = setSingleton nameCmp r.ident
    }
end

lang DTCTypeOfLam = LamAst + DTCTypeOfBase
  sem typeOfH env =
  | TmLam (r & {tyAnnot = TyUnknown _}) ->
    result.err (DTCAnotError (Some r.info))
  | TmLam r ->
    let env = dtcEnvInsert r.ident r.tyAnnot env in
    result.bind (typeOfHPromote env r.body)
      (lam body.
        result.ok {
          e = Det (),
          ty = ityarrowe_ r.info r.tyAnnot body.ty body.e,
          fv = setRemove r.ident body.fv
        })
end

lang DTCTypeOfApp = AppAst + DTCFunTypeAst + FreeVars + DTCTypeOfBase
  sem typeOfH env =
  | TmApp r ->
    result.bind (typeOfH env r.lhs) (lam lhs.
      match lhs with {ty = TyArrowE arr} then
        result.bind (typeOfHPromote env r.rhs) (lam rhs.
          if subtype (rhs.ty, arr.from) then
            resultOK [lhs.e, arr.e, rhs.e] arr.to [lhs.fv, rhs.fv]
          else
            result.err
              (DTCParameterError (Some (infoTm r.rhs, (arr.from, rhs.ty)))))
      else result.err (DTCArrowError (Some (infoTm r.lhs, lhs.ty))))
end

lang DTCTypeOfLet = DTCTypeOfLam + DTCTypeOfApp + UnknownTypeAst
  sem typeOfH env =
  | TmLet r ->
    let wi = withInfo r.info in
    typeOfH env (wi (app_ (wi (nlam_ r.ident r.tyAnnot r.inexpr)) r.body))
  | TmLet (r & {tyAnnot = TyUnknown _}) ->
    result.bind (typeOfHPromote env r.body) (lam body.
      typeOfH env (TmLet { r with tyAnnot = body.ty }))
end

lang DTCTyConst = TyConst + DTCTypeError + DTCTypeOfBase

  sem dtcConstType : Info -> Const -> Result DTCTypeError DTCTypeError Type
  sem dtcConstType info =
  | const ->
    -- NOTE(oerikss, 2024-10-09): By default we type constant functions as
    -- deterministic and non-differential.
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
      (lam ty. result.ok { e = Det (), ty = ty, fv = setEmpty nameCmp })
end

lang DTCTypeOfSeq = SeqAst + SeqTypeAst + DTCTypeOfBase
  sem typeOfH env =
  | TmSeq (r & {tms = []}) ->
    result.ok {
      e = Det (),
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
    e = Det (), ty = TyBot { info = r.info }, fv = setEmpty nameCmp }
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
    result.bind
      (typeOfH env r.model)
      (lam model.
        -- NOTE(oerikss, 2024-10-21): For brevity we refrain from type checking
        -- the inference method arguments. This is anyways type-checked by the
        -- standard core PPL type-checker.
        let err =
          result.err
            (DTCParameterError
              (Some (infoTm r.model,
                     (tyarrowe_ tyunit_ (tyvar_ "a") (Rnd ()), model.ty))))
        in
        match model with {ty = TyArrowE (arr & {from = TyRecord rr})} then
          if mapIsEmpty rr.fields then
            result.ok {
              model with ty = TyDist { info = r.info, ty = arr.to }
            }
          else err
        else err)
end

lang DTCTypeOfAssume = Assume + DTCTypeOfBase
  sem typeOfH env =
  | TmAssume r ->
    result.bind (typeOfH env r.dist) (lam dist.
      match dist with {ty = TyDist distr} then
        let c = dtcEnvMinc (dtcEnvWeaken dist.fv env) in
        result.ok { dist with e = Rnd (), ty = mulcType c distr.ty }
      else
        result.err
          (DTCParameterError
            (Some (infoTm r.dist, (tydist_ (tyvar_ "a"), dist.ty)))))
end

lang DTCTypeOfObserve = Observe + DTCTypeOfBase
  sem typeOfH env =
  | TmObserve r ->
    result.bind2 (typeOfHPromote env r.value) (typeOfH env r.dist)
      (lam value. lam dist.
        match dist with {ty = TyDist {ty = suppTy}} then
          let tys = (value.ty, suppTy) in
          if subtype tys then
            resultOK [value.e, dist.e] (tyWithInfo r.info tyunit_)
              [value.fv, dist.fv]
          else
            result.err (DTCParameterError (Some (infoTm r.value, tys)))
        else
          result.err
            (DTCParameterError
              (Some (infoTm r.dist, (dist.ty, tydist_ value.ty)))))
end

lang DTCTypeOfWeight = Weight + DTCTypeOfBase
  sem typeOfH env =
  | TmWeight r ->
    result.bind (typeOfHPromote env r.weight) (lam weight.
      let tys = (weight.ty, tyfloatc_ (N ())) in
      if subtype tys then
        result.ok {
          weight with e = Rnd (), ty = tyWithInfo r.info tyunit_
        }
      else result.err (DTCParameterError (Some (infoTm r.weight, tys))))
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
               match t with (i, t) in
               if subtype t then result.ok ()
               else result.err (DTCParameterError (Some (i, (t.1, t.0)))))
             () (zip (map infoTm params) (zip tys paramTys)))
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
    result.bind2 (typeOfH env r.fn) (typeOfHPromote env r.arg) (lam fn. lam arg.
      match fn with {ty = TyArrowE (arr & {e = Det _})} then
        let tys = (arg.ty, arr.from) in
        if and (dtcLeqc (maxcType arr.from) (P ())) (isIsomorficToRn arr.to)
        then
          if subtype tys then
            resultOK [fn.e, arg.e]
              (ityarrowe_ r.info (setC (A ()) arr.from) arr.to (Det ()))
              [fn.fv, arg.fv]
          else result.err (DTCParameterError (Some (infoTm r.arg, tys)))
        else result.err (DTCDiffFnError (Some (infoTm r.fn, fn.ty)))
      else result.err (DTCDiffFnError (Some (infoTm r.fn, fn.ty))))
end

lang DTCTypeOfSolveODE = SolveODE + IsIsomorficToRn + DTCTypeOfBase
  sem typeOfH env =
  | TmSolveODE r ->
    -- NOTE(oerikss, 2024-10-21): For brevity we refrain from type checking
    -- the inference method arguments. This is anyways type-checked by the
    -- standard core PPL type-checker.
    result.bind3
      (typeOfH env r.model)
      (typeOfHPromote env r.init)
      (typeOfHPromote env r.endTime)
      (lam model. lam init. lam endTime.
        match model
          with
          {ty = TyArrowE (arr1 & {
            from = TyFloatC _, to = TyArrowE (arr2 & {e = Det _}), e = Det _})}
        then
          if allb [
            isIsomorficToRn arr2.from,
            isIsomorficToRn arr2.to
          ] then
            let ty =
              optionGetOrElse (lam. error "impossible")
                (meetType (arr2.from, arr2.to))
            in
            let tys =
              (model.ty,
               TyArrowE { arr1 with to = tyarrowe_ ty ty (Det ())})
            in
            if subtype tys then
              let tys = (init.ty, ty) in
              if subtype tys then
                let tys = (endTime.ty, tyfloatc_ (P ())) in
                if subtype tys then
                  resultOK [model.e, init.e, endTime.e] ty
                    [model.fv, init.fv, endTime.fv]
                else
                  result.err (DTCParameterError (Some (infoTm r.endTime, tys)))
              else
                result.err (DTCParameterError (Some (infoTm r.init, tys)))
            else
              result.err (DTCParameterError (Some (infoTm r.model, tys)))
          else
            result.err
              (DTCSolveODEModelError (Some (infoTm r.model, model.ty)))
        else
          result.err
            (DTCSolveODEModelError (Some (infoTm r.model, model.ty))))
end

-- ┌───────────────────┐
-- │ Type of Constants │
-- └───────────────────┘

lang DTCFloatType = DTCTyConst
  sem dtcConstType info =| CFloat _ -> result.ok (ityfloatc_ info (N ()))
end

lang DTCArithFloatType = ArithFloatAst + DTCTyConst
  sem dtcConstType info =
  | CAddf _ | CSubf _ | CMulf _ | CDivf _ ->
    let tyfloata = ityfloatc_ info (A ()) in
    let tyarrowed = lam from. lam to. ityarrowe_ info from to (Det ()) in
    result.ok (tyarrowed tyfloata (tyarrowed tyfloata tyfloata))
  | CNegf _ ->
    let tyfloata = ityfloatc_ info (A ()) in
    result.ok (ityarrowe_ info tyfloata tyfloata (Det ()))
end

lang DTCElementaryFunctionsType = ElementaryFunctions + DTCTyConst
  sem dtcConstType info =
  | CSin _ | CCos _ | CSqrt _  | CExp _ | CLog _ | CPow _ ->
    let tyfloata = ityfloatc_ info (A ()) in
    result.ok (ityarrowe_ info tyfloata tyfloata (Det ()))
end

lang DTCCmpFloatAstType = CmpFloatAst + DTCTyConst
  sem dtcConstType info =
  | CEqf _ | CLtf _ | CLeqf _ | CGtf _ | CGeqf _ | CNeqf _ ->
    let tyfloatp = ityfloatc_ info (P ()) in
    let tyarrowed = lam from. lam to. ityarrowe_ info from to (Det ()) in
    result.ok (tyarrowed tyfloatp (tyarrowed tyfloatp (itybool_ info)))
end

let _iarrd = lam info. lam from. lam to.
  use DTCAst in ityarrowe_ info from to (Det ())
let _arrd = lam from. lam to.
  use DTCAst in ityarrowe_ (NoInfo ()) from to (Det ())
let _a = tyvar_ "a"
let _b = tyvar_ "b"

lang DTCSeqOpAstType = SeqOpAst + DTCTypeOfConst
  sem _seqparamerr tm =| ty ->
    result.err (DTCParameterError (Some (infoTm tm, (tyseq_ _a, ty))))

  sem _paramerr tm ty1 =| ty2 ->
    result.err (DTCParameterError (Some (infoTm tm, (ty1, ty2))))

    -- NOTE(oerikss, 2024-10-21): We can handle polymorphic sequence operations if
  -- they are applied to enough arguments.
  sem typeOfH env =
  | TmApp (r & {lhs = TmConst {val = CSet _}}) ->
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      match rhs with {ty = TySeq seqr} then
        result.ok {
          rhs with
          ty =
            foldr1 (_iarrd r.info) [ityint_ r.info, seqr.ty, rhs.ty]
        }
      else _seqparamerr r.rhs rhs.ty)
  | TmApp (r & {lhs = TmConst {val = CGet _}}) ->
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      match rhs with {ty = TySeq seqr} then
        result.ok { rhs with ty = _iarrd r.info (ityint_ r.info) seqr.ty }
      else _seqparamerr r.rhs rhs.ty)
  | TmApp (r & {lhs = TmConst {val = CCons _}}) ->
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      let seq = ityseq_ r.info rhs.ty in
      result.ok { rhs with ty = _iarrd r.info seq seq })
  | TmApp (r & {lhs = TmConst {val = CSnoc _}}) ->
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      match rhs with {ty = TySeq seqr} then
        result.ok { rhs with ty = _iarrd r.info seqr.ty rhs.ty }
      else _seqparamerr r.rhs rhs.ty)
  | TmApp (r & {lhs = TmConst {val = CConcat _ }}) ->
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      match rhs with {ty = TySeq _} then
        result.ok { rhs with ty = _iarrd r.info rhs.ty rhs.ty }
      else  _seqparamerr r.rhs rhs.ty)
  | TmApp (r & {lhs = TmConst {val = CLength _}}) ->
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      match rhs with {ty = TySeq _} then
        result.ok { rhs with ty = ityint_ r.info }
      else _seqparamerr r.rhs rhs.ty)
  | TmApp (r & {lhs = TmConst {val = CHead _}}) ->
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      match rhs with {ty = TySeq seqr} then
        result.ok { rhs with ty = seqr.ty }
      else _seqparamerr r.rhs rhs.ty)
  | TmApp (r & {lhs = TmConst {val = CTail _ | CReverse _}}) ->
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      match rhs with {ty = TySeq _} then
        result.ok { rhs with ty = rhs.ty }
      else _seqparamerr r.rhs rhs.ty)
  | TmApp (r & {lhs = TmConst {val = CNull _ | CIsList _ | CIsRope _}}) ->
    result.bind (typeOfH env r.rhs) (lam rhs.
      match rhs with {ty = TySeq _} then
        result.ok { rhs with ty = itybool_ r.info }
      else _seqparamerr r.rhs rhs.ty)
  | TmApp (r & {lhs = TmConst {val = CMap _}}) ->
    result.bind (typeOfH env r.rhs) (lam rhs.
      match rhs with {ty = TyArrowE arr} then
        let seq = ityseq_ r.info in
        result.ok {
          rhs with
          ty = ityarrowe_ r.info (seq arr.from) (seq arr.to) arr.e
        }
      else _paramerr r.rhs (_arrd _a _b) rhs.ty)
  | TmApp (r & {lhs = TmConst {val = CMapi _}}) ->
    result.bind (typeOfH env r.rhs) (lam rhs.
      match rhs with
        {ty = TyArrowE (arr1 & {from = TyInt _, to = TyArrowE arr2})}
      then
        let seq = ityseq_ r.info in
        result.ok {
          rhs with
          ty = ityarrowe_ r.info (seq arr2.from) (seq arr2.to)
                 (dtcMule arr1.e arr2.e)
        }
      else _paramerr r.rhs (foldr1 _arrd [tyint_, _a, _b]) rhs.ty)
  | TmApp (r & {lhs = TmConst {val = CIter _}}) ->
    result.bind (typeOfH env r.rhs) (lam rhs.
      let err = _paramerr r.rhs (_arrd _a tyunit_) rhs.ty in
      match rhs with {ty = TyArrowE (arr & {to = TyRecord rr})} then
        if mapIsEmpty rr.fields then
          result.ok {
          rhs with
          ty = ityarrowe_ r.info (ityseq_ r.info arr.from) arr.to arr.e
        }
        else err
      else err)
  | TmApp (r & {lhs = TmConst {val = CIteri _}}) ->
    result.bind (typeOfH env r.rhs) (lam rhs.
      let err = _paramerr r.rhs (foldr1 _arrd [tyint_, _a, tyunit_]) rhs.ty in
      match rhs with
        {ty = TyArrowE (arr1 & {
          from = TyInt _, to = TyArrowE (arr2 & {to = TyRecord rr})})}
      then
        if mapIsEmpty rr.fields then
          let seq = ityseq_ r.info in
          result.ok {
            rhs with
            ty = ityarrowe_ r.info (seq arr2.from) arr2.to
                   (dtcMule arr1.e arr2.e)
          }
        else err
      else err)
  | TmApp (r & {lhs = TmConst {val = CFoldl _}}) ->
    result.bind (typeOfH env r.rhs) (lam rhs.
      let err = _paramerr r.rhs (foldr1 _arrd [_a, _b, _a]) rhs.ty in
      match rhs with {ty = TyArrowE (arr1 & {to = TyArrowE arr2})} then
        optionMapOr err
          (lam ty.
            let arr = ityarrowe_ r.info in
            result.ok {
              rhs with
              ty =
                arr
                  ty
                  (arr (ityseq_ r.info arr2.from) ty (dtcMule arr1.e arr2.e))
                  (Det ())
            })
          (joinType (arr1.from, arr2.to))
      else err)
  | TmApp (r & {lhs = TmConst {val = CFoldr _}}) ->
    result.bind (typeOfH env r.rhs) (lam rhs.
      let err = _paramerr r.rhs (foldr1 _arrd [_a, _b, _b]) rhs.ty in
      match rhs with {ty = TyArrowE (arr1 & {to = TyArrowE arr2})} then
        optionMapOr err
          (lam ty.
            let arr = ityarrowe_ r.info in
            result.ok {
              rhs with
              ty =
                arr
                  ty
                  (arr (ityseq_ r.info arr1.from) ty (dtcMule arr1.e arr2.e))
                  (Det ())
            })
          (joinType (arr2.from, arr2.to))
      else err)
  | TmApp (r2 & {lhs = TmApp (r1 & {
    lhs = TmConst {val = CCreate _ | CCreateList _ | CCreateRope _}})}) ->
    result.bind2 (typeOfH env r1.rhs) (typeOfH env r2.rhs) (lam rhs1. lam rhs2.
      match rhs1.ty with TyInt _ then
        match rhs2.ty with TyArrowE (arr & {from = TyInt _}) then
          resultOK [rhs1.e, arr.e] (ityseq_ r2.info arr.to) [rhs1.fv, rhs2.fv]
        else _paramerr r2.rhs (_arrd tyint_ _a) rhs2.ty
      else _paramerr r1.rhs tyint_ rhs1.ty)
  | TmApp (r & {lhs = TmConst {val = CSplitAt _}}) ->
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      match rhs with {ty = TySeq _} then
        result.ok {
          rhs with
          ty = _iarrd r.info (ityint_ r.info)
                 (itytuple_ r.info [rhs.ty, rhs.ty])
        }
      else _seqparamerr r.rhs r.ty)
  | TmApp (r & {lhs = TmConst {val = CSubsequence _}}) ->
    result.bind (typeOfHPromote env r.rhs) (lam rhs.
      let int = ityint_ r.info in
      match rhs with {ty = TySeq _} then
        result.ok { rhs with ty = foldr1 (_iarrd r.info) [int, int, rhs.ty] }
      else _seqparamerr r.rhs r.ty)
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
  | (TySeq tr, PatSeqEdge pr) ->
    let patSeqTot = lam pats.
      PatSeqTot { pats = pats, info = pr.info, ty = pr.ty }
    in
    result.bind
      (dtcTypeCheckPat env patEnv (TySeq tr, patSeqTot pr.prefix))
      (lam patEnv.
        result.bind
          (dtcTypeCheckPat env patEnv (tr.ty, ipatNamed_ pr.info pr.middle))
          (lam patEnv.
            dtcTypeCheckPat env patEnv (TySeq tr, patSeqTot pr.postfix)))
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
  DTCTypeOfDist + DTCTypeOfDiff + DTCTypeOfSolveODE +

  -- Constants
  DTCTyConst + DTCFloatType + DTCArithFloatType + DTCElementaryFunctionsType +
  DTCCmpFloatAstType + DTCSeqOpAstType +

  -- Patterns
  DTCPatTypeCheckAll
end

lang TestLang = DTCTypeOf + MExprPPL end

mexpr

use TestLang in

-- Drop "module name" for brevity
let det = Det () in
let rnd = Rnd () in
let a = (A ()) in
let p = (P ()) in
let n = (N ()) in

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
  tyfloatc_ a, tyfloatc_ p, tyfloatc_ n,
  tyarrowe_ (tyfloatc_ a) (tyfloatc_ a) det,
  tyarrowe_ (tyfloatc_ a) (tyfloatc_ a) rnd,
  tytuple_ [tyfloatc_ a, tyfloatc_ p, tyfloatc_ n],
  tyseq_ (tyfloatc_ a),
  tyint_,
  tybool_,
  tydist_ (tyfloatc_ a)
] in

-- ┌───────────────────────┐
-- │ Test eraseDecorations │
-- └───────────────────────┘

utest eraseDecorations (tyfloatc_ a) with tyfloat_ using eqType in
utest
  eraseDecorations
    (tyarrowe_
       (tyfloatc_ a)
       (tyarrowe_ (tychar_) (tyfloatc_ a) det)
       det)
  with tyarrow_ tyfloat_ (tyarrow_ tychar_ tyfloat_) using eqType
in

-- ┌────────────────┐
-- │ Test leqcType  │
-- └────────────────┘

utest leqcType a (tyfloatc_ a) with true in
utest leqcType a (tyfloatc_ p) with true in
utest leqcType p (tyfloatc_ a) with false in
let rhs = tytuple_ [
  tyfloatc_ p,
  tyseq_ (tyfloatc_ n),
  tyarrowe_ (tyfloatc_ a) (tyfloatc_ a) det
] in
utest leqcType a rhs with true in
utest leqcType p rhs with true in
utest leqcType n rhs with false in

-- ┌─────────────────┐
-- │ Test dtcLeqcEnv │
-- └─────────────────┘

utest dtcLeqcEnv a (dtcEnvOfSeq []) with true in
utest dtcLeqcEnv a (dtcEnvOfSeq [(_x, tyfloatc_ a)]) with true in
let env = dtcEnvOfSeq [(_x, tyfloatc_ p), (_y, tyfloatc_ n)] in
utest dtcLeqcEnv a env with true in
utest dtcLeqcEnv p env with true in
utest dtcLeqcEnv n env with false in
utest
  dtcLeqcEnv n
    (dtcEnvOfSeq [(_x, (tyarrowe_ (tychar_) (tyfloatc_ a) det))])
  with true
in

-- ┌───────────────┐
-- │ Test mulcType │
-- └───────────────┘

utest mulcType a (tyfloatc_ a) with tyfloatc_ a using eqType in
utest mulcType a (tyfloatc_ p) with tyfloatc_ p using eqType in
utest mulcType p (tyfloatc_ a) with tyfloatc_ p using eqType in
utest mulcType n (tyarrowe_ (tyfloatc_ a) (tyfloatc_ a) det) with
  tyarrowe_ (tyfloatc_ a) (tyfloatc_ a) det using eqType
in
utest mulcType p (tytuple_ [tyfloatc_ a, tyfloatc_ n]) with
  tytuple_ [tyfloatc_ p, tyfloatc_ n] using eqType
in
utest mulcType p (tyseq_ (tyfloatc_ a))
  with (tyseq_ (tyfloatc_ p)) using eqType
in
utest mulcType p (tydist_ (tyfloatc_ a))
  with (tydist_ (tyfloatc_ a)) using eqType
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

utest _subtype a a with true in
utest _subtype a p with false in
utest _subtype a n with false in
utest _subtype p a with true in
utest _subtype p p with true in
utest _subtype p n with false in
utest _subtype n a with true in
utest _subtype n p with true in
utest _subtype n n with true in

utest subtype (tyfloatc_ a, tytuple_ [tyfloatc_ a]) with false in

-- Sequences
utest subtype (tyseq_ (tyfloatc_ p), tyseq_ (tyfloatc_ a)) with true in

-- Records
let tup2 = lam c1. lam c2. tytuple_ [tyfloatc_ c1, tyfloatc_ c2] in
let tup3 = lam c1. lam c2. lam c3.
  tytuple_ [tyfloatc_ c1, tyfloatc_ c2, tyfloatc_ c2]
in

utest subtype (tup2 a a, tup2 a a) with true in
utest subtype (tup2 a a, tup3 a a a) with false in
utest subtype (tup3 a a a, tup2 a a) with false in
utest subtype (tup2 p n, tup2 a p) with true in
utest subtype (tup2 a a, tup2 a p) with false in

-- Arrows
let arr = lam c1. lam c2. lam e.
  tyarrowe_ (tyfloatc_ c1) (tyfloatc_ c2) e
in

utest subtype (arr a a det, arr a a det) with true in
utest subtype (arr a a det, arr a a rnd) with true in
utest subtype (arr a a rnd, arr a a rnd) with true in
utest subtype (arr a a rnd, arr a a det) with false in
utest subtype (arr a p det, arr a a det) with true in
utest subtype (arr a a det, arr p a det) with true in

-- Type variables
utest subtype (tyvar_ "X", tyvar_ "X") with true in
utest subtype (tyvar_ "X", tyvar_ "Y") with false in

-- Distributions
let dist = lam c. tydist_ (tyfloatc_ c) in

utest subtype (dist a, dist a) with true in
utest subtype (dist a, dist p) with false in

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

utest _joinType a a with Some (tyfloatc_ a) using eq in
utest _joinType a p with Some (tyfloatc_ a) using eq in
utest _joinType p a with Some (tyfloatc_ a) using eq in
utest _joinType a n with Some (tyfloatc_ a) using eq in
utest _joinType n a with Some (tyfloatc_ a) using eq in
utest _joinType p p with Some (tyfloatc_ p) using eq in
utest _joinType n p with Some (tyfloatc_ p) using eq in
utest _joinType p n with Some (tyfloatc_ p) using eq in
utest _joinType n n with Some (tyfloatc_ n) using eq in

let _meetType = lam c1. lam c2. meetType (tyfloatc_ c1, tyfloatc_ c2) in

utest _meetType a a with Some (tyfloatc_ a) using eq in
utest _meetType a p with Some (tyfloatc_ p) using eq in
utest _meetType p a with Some (tyfloatc_ p) using eq in
utest _meetType a n with Some (tyfloatc_ n) using eq in
utest _meetType n a with Some (tyfloatc_ n) using eq in
utest _meetType p p with Some (tyfloatc_ p) using eq in
utest _meetType n p with Some (tyfloatc_ n) using eq in
utest _meetType p n with Some (tyfloatc_ n) using eq in
utest _meetType n n with Some (tyfloatc_ n) using eq in

-- Sequences
let seq = lam c. tyseq_ (tyfloatc_ c) in

utest joinType (seq a, seq a) with Some (seq a) using eq in
utest joinType (seq a, seq p) with Some (seq a) using eq in
utest joinType (seq p, seq a) with Some (seq a) using eq in
utest joinType (seq p, seq p) with Some (seq p) using eq in
utest meetType (seq a, seq a) with Some (seq a) using eq in
utest meetType (seq a, seq p) with Some (seq p) using eq in
utest meetType (seq p, seq a) with Some (seq p) using eq in
utest meetType (seq p, seq p) with Some (seq p) using eq in
utest meetType (seq p, tyfloatc_ a) with None () using eq in

-- Records
utest joinType (tup2 a a, tup2 a a) with Some (tup2 a a) using eq in
utest joinType (tup2 a a, tup3 a a a) with None () using eq in
utest joinType (tup3 a a a, tup2 a a) with None () using eq in
utest joinType (tup2 p n, tup2 a p) with Some (tup2 a p) using eq in
utest joinType (tup2 a a, tup2 a p) with Some (tup2 a a) using eq in

utest meetType (tup2 a a, tup2 a a) with Some (tup2 a a) using eq in
utest meetType (tup2 a a, tup3 a a a) with None () using eq in
utest meetType (tup3 a a a, tup2 a a) with None () using eq in
utest meetType (tup2 p n, tup2 a p) with Some (tup2 p n) using eq in
utest meetType (tup2 a a, tup2 a p) with Some (tup2 a p) using eq in

-- Arrows
let arr = tyarrowe_ (tyfloatc_ a) (tyfloatc_ a) in
let _joinType = lam e1. lam e2. joinType (arr e1, arr e2) in

utest _joinType det det with Some (arr det) using eq in
utest _joinType det rnd with Some (arr rnd) using eq in
utest _joinType rnd det with Some (arr rnd) using eq in
utest _joinType rnd rnd with Some (arr rnd) using eq in

let _meetType = lam e1. lam e2. meetType (arr e1, arr e2) in

utest _meetType det det with Some (arr det) using eq in
utest _meetType det rnd with Some (arr det) using eq in
utest _meetType rnd det with Some (arr det) using eq in
utest _meetType rnd rnd with Some (arr rnd) using eq in

let arr = lam c. tyarrowe_ (tyfloatc_ c) (tyfloatc_ a) det in
let _joinType = lam c1. lam c2. joinType (arr c1, arr c2) in

utest _joinType a p with Some (arr p) using eq in
utest _joinType p a with Some (arr p) using eq in
utest _joinType a n with Some (arr n) using eq in
utest _joinType n a with Some (arr n) using eq in
utest _joinType p n with Some (arr n) using eq in
utest _joinType n p with Some (arr n) using eq in
utest _joinType p p with Some (arr p) using eq in
utest _joinType n n with Some (arr n) using eq in

let _meetType = lam c1. lam c2. meetType (arr c1, arr c2) in

utest _meetType a p with Some (arr a) using eq in
utest _meetType p a with Some (arr a) using eq in
utest _meetType a n with Some (arr a) using eq in
utest _meetType n a with Some (arr a) using eq in
utest _meetType p n with Some (arr p) using eq in
utest _meetType n p with Some (arr p) using eq in
utest _meetType p p with Some (arr p) using eq in
utest _meetType n n with Some (arr n) using eq in

let arr = lam c. tyarrowe_ (tyfloatc_ a) (tyfloatc_ c) det in
let _joinType = lam c1. lam c2. joinType (arr c1, arr c2) in

utest _joinType a p with Some (arr a) using eq in
utest _joinType p a with Some (arr a) using eq in
utest _joinType a n with Some (arr a) using eq in
utest _joinType n a with Some (arr a) using eq in
utest _joinType p n with Some (arr p) using eq in
utest _joinType n p with Some (arr p) using eq in
utest _joinType p p with Some (arr p) using eq in
utest _joinType n n with Some (arr n) using eq in

let _meetType = lam c1. lam c2. meetType (arr c1, arr c2) in

utest _meetType a p with Some (arr p) using eq in
utest _meetType p a with Some (arr p) using eq in
utest _meetType a n with Some (arr n) using eq in
utest _meetType n a with Some (arr n) using eq in
utest _meetType p n with Some (arr n) using eq in
utest _meetType n p with Some (arr n) using eq in
utest _meetType p p with Some (arr p) using eq in
utest _meetType n n with Some (arr n) using eq in

-- Type variables
utest joinType (tyvar_ "X", tyvar_ "X") with Some (tyvar_ "X") using eq in
utest joinType (tyvar_ "X", tyvar_ "Y") with None () using eq in
utest meetType (tyvar_ "X", tyvar_ "X") with Some (tyvar_ "X") using eq in
utest meetType (tyvar_ "X", tyvar_ "Y") with None () using eq in

-- Distributions
let dist = lam c. tydist_ (tyfloatc_ c) in

utest joinType (dist a, dist a) with Some (dist a) using eq in
utest joinType (dist a, dist p) with Some (dist a) using eq in
utest joinType (dist p, dist a) with Some (dist a) using eq in
utest joinType (dist p, dist p) with Some (dist p) using eq in
utest meetType (dist a, dist a) with Some (dist a) using eq in
utest meetType (dist a, dist p) with Some (dist p) using eq in
utest meetType (dist p, dist a) with Some (dist p) using eq in
utest meetType (dist p, dist p) with Some (dist p) using eq in

-- ┌───────────────┐
-- │ Test mincType │
-- └───────────────┘

-- Bottom
utest mincType tybot_ with n in

-- Float
let _mincType = lam c. mincType (tyfloatc_ c) in

utest _mincType a with a in
utest _mincType p with p in
utest _mincType n with n in

-- Seqences
let _mincType = lam c. mincType (tyseq_ (tyfloatc_ c)) in

utest _mincType a with a in
utest _mincType p with p in
utest _mincType n with n in

-- Records
let _mincType = lam c1. lam c2. mincType (tytuple_ [tyfloatc_ c1, tyfloatc_ c2]) in

utest _mincType a a with a in
utest _mincType a p with a in
utest _mincType a n with a in
utest _mincType p a with a in
utest _mincType p p with p in
utest _mincType p n with p in
utest _mincType n a with a in
utest _mincType n p with p in
utest _mincType n n with n in

-- Arrows
let _mincType = lam c1. lam c2.
  mincType (tyarrowe_ (tyfloatc_ c1) (tyfloatc_ c2) (Det ()))
in

utest _mincType a a with n in
utest _mincType a p with n in
utest _mincType a n with n in
utest _mincType p a with n in
utest _mincType p p with n in
utest _mincType p n with n in
utest _mincType n a with n in
utest _mincType n p with n in
utest _mincType n n with n in

-- Type variables
utest mincType (tyvar_ "X") with n in

-- Distributions
let _mincType = lam c. mincType (tydist_ (tyfloatc_ c)) in

utest _mincType a with n in
utest _mincType p with n in
utest _mincType n with n in

-- ┌─────────────────┐
-- │ Test dtcEnvMinc │
-- └─────────────────┘

let genC = lam.
  switch randIntU 0 2
  case 0 then A ()
  case 1 then P ()
  case 2 then N ()
  end
in

let genEnv = lam.
  dtcEnvOfSeq [
    (_x, tyfloatc_ (genC ())),
    (_y, tyfloatc_ (genC ())),
    (_z, tyfloatc_ (genC ())),
    (_f, tyarrowe_ (tyfloatc_ a) (tyfloatc_ a) det)
    -- (_g, tydist_ (tyfloatc_ a))
  ]
in

repeat
  (lam. let env = genEnv () in
      let c1 = dtcEnvMinc env in
      -- Exit on first failing test
      let onFail = lam. lam.
        error "Failed randomized test"
      in
      utest dtcLeqcEnv c1 env with true
        using and else onFail
      in
      -- Test that c1 is indeed the maximum coeffect modifier that fulfuills
      -- `dtcLeqcEnv c1 env`
      iter (lam c2.
        if not (dtcLeqc c2 c1) then
          utest dtcLeqcEnv c2 env with false
            using (lam a. lam b. and (not a) (not b)) else onFail
          in ()
        else ())
        [A (), P (), N ()])
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

-- Shorthand types
let arr = lam ps. lam ret. foldr (lam t. lam to. tyarrowe_ t.0 to t.1) ret ps in
let arrd = lam ps. arr (map (lam p. (p, det)) ps) in
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
  with Right (det, arr [(tyint_, det)] tyint_)
  using eq
in

utest _typeOf [(_x, tyint_)] (app_ x x)
  with Left [DTCArrowError (None ())]
  using eq
in

utest _typeOf [(_x, tyint_)] (bind_ (nulet_ _y x) y)
  with Right (det, tyint_)
  using eq
in

-- Test effect propagation
utest _typeOf [(_f, arr [(tyint_, rnd)] tyint_), (_x, tyint_)] (f [x])
  with Right (rnd, tyint_)
  using eq
in

-- Test subtyping and promotion
utest _typeOf [(_f, arrd [flt a] (flt a)), (_x, flt a)] (f [x])
  with Right (det, flt a)
  using eq
in

utest _typeOf [(_f, arrd [flt a] (flt a)), (_x, flt p)] (f [x])
  with Right (det, flt a)
  using eq
in

utest _typeOf [(_f, arrd [flt a] tyint_), (_x, tyint_)] (f [x])
  with Left [DTCParameterError (None ())]
  using eq
in

let env = [
  (_f, arrd [flt a, flt a] (flt a)),
  (_g, arrd [flt p, flt p] (flt p)),
  (_x, flt p),
  (_y, flt a)
] in

utest
  _typeOf env  (f [g [f [x, x], x], y])
  with Right (det, flt a)
  using eq
in

utest
  _typeOf env (f [g [f [x, x], y], y])
  with Left [DTCParameterError (None ())]
  using eq
in

utest
  _typeOf env (f [g [f [x, y], x], y])
  with Left [DTCParameterError (None ())]
  using eq
in

utest
  _typeOf [] (addf_ (float_ 1.) (float_ 1.))
  with Right (det, flt a)
  using eq
in

let env = [
  (_f, arrd [flt a] (flt a)),
  (_g, arrd [flt n] (flt n))
] in

utest
  _typeOf env
    (app_
       (lam_ [(_h, arrd [flt a] (flt n))] (lam_ [(_y, flt a)] (g [h [y]])))
       (lam_ [(_x, flt a)] (f [float_ 1.])))
  with Right (det, arrd [flt a] (flt n))
  using eq
in

let env = [
  (_f, arrd [flt n, flt n] (flt n)),
  (_x, flt n),
  (_y, flt a)
] in

utest
  _typeOf env (addf_ (f [addf_ x (float_ 1.), x]) y)
  with Right (det, flt a)
  using eq
in

let env = [
  (_f, arrd [flt n, flt n] (flt n)),
  (_x, flt p),
  (_y, flt a)
] in

utest
  _typeOf env (addf_ (f [addf_ x (float_ 1.), x]) y)
  with Left [DTCParameterError (None ())]
  using eq
in

-- Test sequence

utest
  _typeOf [] (seq_ [])
  with Right (det, tyseq_ (TyBot { info = NoInfo () }))
  using eq
in

utest
  _typeOf [(_x, flt a)] (seq_ [x])
  with Right (det, tyseq_ (flt a))
  using eq
in

utest
  _typeOf [(_x, flt a), (_y, flt p)] (seq_ [x, y])
  with Right (det, tyseq_ (flt a))
  using eq
in

utest
  _typeOf [
    (_f, arr [(flt a, rnd)] (flt a)),
    (_g, arr [(flt a, det)] (flt a)),
    (_x, flt p),
    (_y, flt n)
  ] (seq_ [f [x], g [y]])
  with Right (rnd, tyseq_ (flt p))
  using eq
in

-- Test records

utest
  _typeOf [] (utuple_ [])
  with Right (det, tytuple_ [])
  using eq
in

utest
  _typeOf [(_x, flt a), (_y, flt p)] (utuple_ [x, y])
  with Right (det, tytuple_ [flt a, flt p])
  using eq
in

utest
  _typeOf [
    (_f, arr [(flt a, rnd)] (flt a)),
    (_g, arr [(flt a, det)] (flt a)),
    (_x, flt p),
    (_y, flt n)
  ] (utuple_ [f [x], g [y]])
  with Right (rnd, tytuple_ [flt p, flt n])
  using eq
in

-- Test never

utest _typeOf [] never_ with Right (det, tybot_) using eq in

-- Test match

let env = [
  (_x, flt a)
] in

utest
  _typeOf env (match_ x (npvar_ _y) y x)
  with Right (det, flt a)
  using eq
in

utest
  _typeOf env (match_ x (npvar_ _y) y (float_ 1.))
  with Right (det, flt a)
  using eq
in

let env = [
  (_f, arrd [flt p, flt p] (flt a)),
  (_g, arr [(flt a, rnd), (flt n, det)] (flt p))
] in

utest
  let f = nvar_ _f in
  let g = nvar_ _g in
  _typeOf env (match_ f pvarw_ f g)
  with Right (det, arr [(flt p, rnd), (flt n, det)] (flt a))
  using eq
in

let env = [
  (_x, tyseq_ (flt a))
] in

utest
  _typeOf env (match_ x (pseqtot_ [npvar_ _y, npvar_ _z]) (seq_ [z, y]) x)
  with Right (det, tyseq_ (flt a))
  using eq
in

utest
  _typeOf env
    (match_ x (pseqedgen_ [npvar_ _y] _z [npvar_ _u])
       (seq_ [z, y]) x)
  with Right (det, tyseq_ (flt a))
  using eq
in

let env = [
  (_x, tytuple_ [flt a, flt p, flt n])
] in

utest
  _typeOf env (tupleproj_ 0 x)
  with Right (det, flt a)
  using eq
in

utest
  _typeOf env (tupleproj_ 1 x)
  with Right (det, flt p)
  using eq
in

utest
  _typeOf env (tupleproj_ 2 x)
  with Right (det, flt n)
  using eq
in

utest
  _typeOf env (tupleproj_ 3 x)
  with Left [DTCPatError (None ())]
  using eq
in

utest
  _typeOf [(_x, tyint_)] (match_ x (pint_ 0) x x)
  with Right (det, tyint_)
  using eq
in

utest
  _typeOf [(_x, tychar_)] (match_ x (pchar_ '0') x x)
  with Right (det, tychar_)
  using eq
in

utest
  _typeOf [(_x, tybool_)] (match_ x ptrue_ x x)
  with Right (det, tybool_)
  using eq
in

utest
  _typeOf [(_x, tychar_)] (match_ x (pint_ 0) x x)
  with Left [DTCPatError (None ())]
  using eq
in

utest
  _typeOf [(_x, tybool_)] (match_ x (pchar_ '0') x x)
  with Left [DTCPatError (None ())]
  using eq
in

utest
  _typeOf [(_x, tyint_)] (match_ x ptrue_ x x)
  with Left [DTCPatError (None ())]
  using eq
in

let env = [
  (_x, flt a),
  (_y, flt p)
] in

let _tm = lam pat.
  match_ (utuple_ [x, y])
    (pat (ptuple_ [npvar_ _z, pvarw_]) (ptuple_ [pvarw_, npvar_ _z]))
    z never_
in

utest _typeOf env (_tm pand_)
  with Right (det, flt a)
  using eq
in

utest _typeOf env (_tm por_)
  with Right (det, flt a)
  using eq
in

let _tm = match_ x (pnot_ (pint_ 0)) x x in

utest _typeOf [(_x, tyint_)] _tm
  with Right (det, tyint_)
  using eq
in

utest _typeOf [(_x, flt a)] _tm
  with Left [DTCPatError (None ())]
  using eq
in

-- Infer

let infer__ = infer_ (Default { runs = int_ 1 }) in

utest _typeOf [(_f, arrd [tyunit_] (flt a))] (infer__ (nvar_ _f))
  with Right (det, tydist_ (flt a))
  using eq
in

utest _typeOf [(_f, arrd [flt a] (flt a))] (infer__ (nvar_ _f))
  with Left [DTCParameterError (None ())]
  using eq
in

let infer__ = infer_ (Default { runs = never_ }) in

utest _typeOf [(_f, arrd [tyunit_] (flt a))] (infer__ (nvar_ _f))
  with Right (det, tydist_ (flt a))
  using eq
in

-- Assume

utest _typeOf [(_x, tydist_ (flt a))] (assume_ x)
  with Right (rnd, flt n)
  using eq
in

utest _typeOf [(_x, flt a)] (assume_ x)
  with Left [DTCParameterError (None ())]
  using eq
in

-- Observe

utest _typeOf [(_x, tydist_ (flt a))] (observe_ (float_ 0.) x)
  with Right (det, tyunit_)
  using eq
in

utest _typeOf [(_x, tydist_ (flt a))] (observe_ (int_ 0) x)
  with Left [DTCParameterError (None ())]
  using eq
in

utest _typeOf [(_x, flt a)] (observe_ (float_ 0.) x)
  with Left [DTCParameterError (None ())]
  using eq
in

-- Weight

utest _typeOf [(_x, flt a)] (weight_ x)
  with Left [DTCParameterError (None ())]
  using eq
in

utest _typeOf [(_x, flt p)] (weight_ x)
  with Left [DTCParameterError (None ())]
  using eq
in

utest _typeOf [(_x, flt n)] (weight_ x)
  with Right (rnd, tyunit_)
  using eq
in

utest _typeOf [] (weight_ (int_ 0))
  with Left [DTCParameterError (None ())]
  using eq
in

-- Dist

utest _typeOf [(_x, flt n), (_y, flt n)] (dist_ (DUniform {a = x, b = y}))
  with Right (det, tydist_ (flt n))
  using eq
in

utest _typeOf [(_x, flt n)] (dist_ (DBernoulli {p = x}))
  with Right (det, tydist_ tybool_)
  using eq
in

utest _typeOf [(_x, flt n)] (dist_ (DPoisson {lambda = x}))
  with Right (det, tydist_ tyint_)
  using eq
in

utest _typeOf [(_x, flt n), (_y, flt n)] (dist_ (DBeta {a = x, b = y}))
  with Right (det, tydist_ (flt n))
  using eq
in

utest _typeOf [(_x, flt n), (_y, flt n)] (dist_ (DGamma {k = x, theta = y}))
  with Right (det, tydist_ (flt n))
  using eq
in

utest _typeOf [(_x, tyseq_ (flt n))] (dist_ (DCategorical {p = x}))
  with Right (det, tydist_ tyint_)
  using eq
in

utest _typeOf [(_x, tyint_), (_y, tyseq_ (flt n))]
        (dist_ (DMultinomial {n = x, p = y}))
  with Right (det, tydist_ (tyseq_ tyint_))
  using eq
in

utest _typeOf [(_x, flt n)] (dist_ (DExponential {rate = x}))
  with Right (det, tydist_ (flt n))
  using eq
in

utest _typeOf [(_x, flt n), (_y, flt n)] (dist_ (DGaussian {mu = x, sigma = y}))
  with Right (det, tydist_ (flt n))
  using eq
in

utest _typeOf [] (dist_ (DWiener { a = unit_ }))
  with Right (det, tydist_ (arrd [flt n] (flt n)))
  using eq
in

utest _typeOf [(_x, flt n)] (dist_ (DExponential {rate = x}))
  with Right (det, tydist_ (flt n))
  using eq
in

utest _typeOf [(_x, (tyseq_ (tytuple_ [flt n, flt n])))]
        (dist_ (DEmpirical {samples = x}))
  with Left [DTCPolyDistError (None ())]
  using eq
in

let _test = lam c.
  _typeOf [(_x, flt c)] (dist_ (DExponential {rate = x}))
in

utest _test a
  with Left [DTCParameterError (None ())]
  using eq
in

utest _test p
  with Left [DTCParameterError (None ())]
  using eq
in

-- Diff

let _test = lam c. _typeOf [
    (_x, tyarrowe_ (flt a) (flt a) det),
    (_y, flt c)
] (diff_ x y) in

utest
  _test a
  with Right (det, tyarrowe_ (flt a) (flt a) det)
  using eq
in

utest
  _test p
  with Right (det, tyarrowe_ (flt a) (flt a) det)
  using eq
in

utest
  _test n
  with Right (det, tyarrowe_ (flt a) (flt a) det)
  using eq
in

let _test = lam c. _typeOf [
    (_x, tyarrowe_ (flt a) (flt c) det),
    (_y, flt a)
] (diff_ x y) in

utest
  _test a
  with Right (det, tyarrowe_ (flt a) (flt a) det)
  using eq
in

utest
  _test p
  with Right (det, tyarrowe_ (flt a) (flt p) det)
  using eq
in

utest
  _test n
  with Right (det, tyarrowe_ (flt a) (flt n) det)
  using eq
in

let _test = lam c. _typeOf [
    (_x, tyarrowe_ (flt c) (flt a) det),
    (_y, flt c)
] (diff_ x y) in

utest
  _test p
  with Right (det, tyarrowe_ (flt a) (flt a) det)
  using eq
in

utest
  _test n
  with Left [DTCDiffFnError (None ())]
  using eq
in

utest
  _typeOf [
    (_x, tyarrowe_ (flt a) (flt a) rnd),
    (_y, flt a)
  ] (diff_ x y)
  with Left [DTCDiffFnError (None ())]
  using eq
in

utest
  _typeOf [
    (_x, tyarrowe_ (tyseq_ (tytuple_ [flt a, tyint_])) (flt a) det),
    (_y, (tyseq_ (tytuple_ [flt a, tyint_])))
  ] (diff_ x y)
  with Left [DTCDiffFnError (None ())]
  using eq
in

utest
  _typeOf [
    (_x, tyarrowe_ (flt a) (tyseq_ (tytuple_ [flt a, tyint_])) det),
    (_y, (flt a))
  ] (diff_ x y)
  with Left [DTCDiffFnError (None ())]
  using eq
in

-- Solve

utest
  _typeOf [
    (_x, arrd [flt a, tytuple_ [flt a, flt a]] (tytuple_ [flt a, flt a])),
    (_y, tytuple_ [flt a, flt a]),
    (_z, flt p)
  ] (solveode_ x y z)
  with Right (det, tytuple_ [flt a, flt a])
  using eq
in

let _test = lam c.
  _typeOf [
    (_x, arrd [flt a, flt p] (flt c)),
    (_y, flt c),
    (_z, flt p)
  ] (solveode_ x y z)
in

utest
  _test a
  with Left [DTCParameterError (None ())]
  using eq
in

utest
  _test p
  with Right (det, flt p)
  using eq
in

utest
  _test n
  with Right (det, flt n)
  using eq
in

let _test = lam c.
  _typeOf [
    (_x, arrd [flt a, flt a] (flt a)),
    (_y, flt a),
    (_z, flt c)
  ] (solveode_ x y z)
in

utest
  _test a
  with Left [DTCParameterError (None ())]
  using eq
in

utest
  _test p
  with Right (det, flt a)
  using eq
in

utest
  _test n
  with Right (det, flt a)
  using eq
in

let _test = lam c.
  _typeOf [
    (_x, arrd [flt a, flt p] (flt p)),
    (_y, flt c),
    (_z, flt p)
  ] (solveode_ x y z)
in

utest
  _test a
  with Left [DTCParameterError (None ())]
  using eq
in

utest
  _test p
  with Right (det, flt p)
  using eq
in

utest
  _test n
  with Right (det, flt p)
  using eq
in

-- NOTE(oerikss, 2024-10-23): This would otherwise allow us to construct
-- an unsafe coerce term:
-- `id = lam z : FloatA. solve (lam FloatA. lam : FloatA. 0.) z 0.` where
-- `id t` coerces any term `t : FloatA` to `FloatN`.
utest
  _typeOf [
    (_x, arrd [flt a, flt a] (flt n)),
    (_y, flt a),
    (_z, flt p)
  ] (solveode_ x y z)
  with Left [DTCParameterError (None ())]
  using eq
in

-- Sequence operations

utest
  _typeOf [
    (_x, tyseq_ (flt a))
  ] (app_ (uconst_ (CSet ())) x)
  with Right (det, arrd [tyint_, flt a] (tyseq_ (flt a)))
  using eq
in

utest
  _typeOf [
    (_x, tyseq_ (flt a))
  ] (app_ (uconst_ (CGet ())) x)
  with Right (det, arrd [tyint_] (flt a))
  using eq
in

utest
  _typeOf [
    (_x, flt a)
  ] (app_ (uconst_ (CCons ())) x)
  with Right (det, arrd [tyseq_ (flt a)] (tyseq_ (flt a)))
  using eq
in

utest
  _typeOf [
    (_x, tyseq_ (flt a))
  ] (app_ (uconst_ (CSnoc ())) x)
  with Right (det, arrd [(flt a)] (tyseq_ (flt a)))
  using eq
in

utest
  _typeOf [
    (_x, tyseq_ (flt a))
  ] (app_ (uconst_ (CConcat ())) x)
  with Right (det, arrd [tyseq_ (flt a)] (tyseq_ (flt a)))
  using eq
in

utest
  _typeOf [
    (_x, tyseq_ (flt a))
  ] (app_ (uconst_ (CLength ())) x)
  with Right (det, tyint_)
  using eq
in

utest
  _typeOf [
    (_x, tyseq_ (flt a))
  ] (app_ (uconst_ (CReverse ())) x)
  with Right (det, tyseq_ (flt a))
  using eq
in

utest
  _typeOf [
    (_x, tyseq_ (flt a))
  ] (app_ (uconst_ (CHead ())) x)
  with Right (det, flt a)
  using eq
in

utest
  _typeOf [
    (_x, tyseq_ (flt a))
  ] (app_ (uconst_ (CTail ())) x)
  with Right (det, tyseq_ (flt a))
  using eq
in

let _test = lam c.
  _typeOf [
    (_x, tyseq_ (flt a))
  ] (app_ (uconst_ c) x)
in

iter
  (lam c. utest _test c with Right (det, tybool_) using eq in ())
  [CNull (), CIsList (), CIsRope ()];

let _test = lam e.
  _typeOf [
    (_x, tyarrowe_ (flt a) (flt p) e)
  ] (app_ (uconst_ (CMap ())) x)
in

let _expected = lam e.
  Right (det, tyarrowe_ (tyseq_ (flt a)) (tyseq_ (flt p)) e)
in

utest _test det with _expected det using eq in
utest _test rnd with _expected rnd using eq in

let _test = lam e1. lam e2.
  _typeOf [
    (_x, arr [(tyint_, e1), (flt a, e2)] (flt p))
  ] (app_ (uconst_ (CMapi ())) x)
in

let _expected = lam e.
  Right (det, tyarrowe_ (tyseq_ (flt a)) (tyseq_ (flt p)) e)
in

utest _test det det with _expected det using eq in
utest _test rnd det with _expected rnd using eq in
utest _test det rnd with _expected rnd using eq in
utest _test rnd rnd with _expected rnd using eq in

let _test = lam e.
  _typeOf [
    (_x, tyarrowe_ (flt a) tyunit_ e)
  ] (app_ (uconst_ (CIter ())) x)
in

let _expected = lam e.
  Right (det, tyarrowe_ (tyseq_ (flt a)) tyunit_ e)
in

utest _test det with _expected det using eq in
utest _test rnd with _expected rnd using eq in

let _test = lam e1. lam e2.
  _typeOf [
    (_x, arr [(tyint_, e1), (flt a, e2)] tyunit_)
  ] (app_ (uconst_ (CIteri ())) x)
in

let _expected = lam e.
  Right (det, tyarrowe_ (tyseq_ (flt a)) tyunit_ e)
in

utest _test det det with _expected det using eq in
utest _test rnd det with _expected rnd using eq in
utest _test det rnd with _expected rnd using eq in
utest _test rnd rnd with _expected rnd using eq in

let _test = lam e1. lam e2.
  _typeOf [
    (_x, arr [(tyint_, e1), (flt a, e2)] tyint_)
  ] (app_ (uconst_ (CFoldl ())) x)
in

let _expected = lam e.
  Right (det, arr [(tyint_, det), (tyseq_ (flt a), e)] (tyint_))
in

utest _test det det with _expected det using eq in
utest _test rnd det with _expected rnd using eq in
utest _test det rnd with _expected rnd using eq in
utest _test rnd rnd with _expected rnd using eq in

let _test = lam e1. lam e2.
  _typeOf [
    (_x, arr [(flt a, e2), (tyint_, e1)] tyint_)
  ] (app_ (uconst_ (CFoldr ())) x)
in

let _expected = lam e.
  Right (det, arr [(tyint_, det), (tyseq_ (flt a), e)] (tyint_))
in

utest _test det det with _expected det using eq in
utest _test rnd det with _expected rnd using eq in
utest _test det rnd with _expected rnd using eq in
utest _test rnd rnd with _expected rnd using eq in

iter
  (lam c.
    let _test = lam e.
      _typeOf [
        (_x, tyint_),
        (_y, arr [(tyint_, e)] (flt a))
      ] (appf2_ (uconst_ c) x y)
    in
    let _expected = lam e. Right (e, tyseq_ (flt a)) in
    utest _test det with _expected det using eq in
    utest _test rnd with _expected rnd using eq in
    ())
  [CCreate (), CCreateList (), CCreateRope ()];

utest
  _typeOf [
    (_x, tyseq_ (flt a))
  ] (app_ (uconst_ (CSplitAt ())) x)
  with Right (det, arrd [tyint_] (tytuple_ [tyseq_ (flt a), tyseq_ (flt a)]))
  using eq
in

utest
  _typeOf [
    (_x, tyseq_ (flt a))
  ] (app_ (uconst_ (CSubsequence ())) x)
  with Right (det, arrd [tyint_, tyint_] (tyseq_ (flt a)))
  using eq
in

-- ┌────────────────┐
-- │ Paper Examples │
-- └────────────────┘

-- Example 10

let env = [
  (_f, arrd [flt n] (flt n))
] in

let _tm = lam c.
  nlam_ _u (tytuple_ [flt n, flt c])
    (matchex_ u (ptuple_ [npvar_ _x, npvar_ _y]) (addf_ (f [x]) y))
in

let _ty = lam c1. lam c2.
  arrd [tytuple_ [flt n, flt c1]] (flt c2)
in

utest _typeOf env (_tm a)
  with Right (det, _ty a a)
  using eq
in

utest _typeOf env (_tm p)
  with Right (det, (_ty p p))
  using eq
in

utest _typeOf env (_tm n)
  with Right (det, (_ty n n))
  using eq
in

let _tm = lam c. lam fst. lam snd.
  nlam_ _z (flt c) (app_ (_tm c) (utuple_ [fst, snd]))
in

let _ty = lam c1. lam c2.
  arrd [flt c1] (flt c2)
in

utest _typeOf env (_tm a (float_ 0.) z)
  with Right (det, _ty a a)
  using eq
in

utest _typeOf env (_tm n z (float_ 0.))
  with Right (det, _ty n n)
  using eq
in

utest _typeOf env (_tm a z (float_ 0.))
  with Left [DTCParameterError (None ())]
  using eq
in

-- Example 11

let _tm = lam c. nlam_ _x (flt c) (if_ (gtf_ x (float_ 0.)) x (negf_ x)) in

utest _typeOf [] (_tm a)
  with Left [DTCParameterError (None ())]
  using eq
in

utest _typeOf [] (_tm p)
  with Right (det, arrd [flt p] (flt p))
  using eq
in

utest _typeOf [] (_tm n)
  with Right (det, arrd [flt n] (flt n))
  using eq
in

()