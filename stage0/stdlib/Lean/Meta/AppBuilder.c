// Lean compiler output
// Module: Lean.Meta.AppBuilder
// Imports: Lean.Structure Lean.Meta.SynthInstance Lean.Meta.Check Lean.Meta.DecLevel
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getProjFnForField_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrueCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetFun___lam__0(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_congrArg_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadLiftIOCoreM;
uint8_t lean_usize_dec_eq(size_t, size_t);
extern uint8_t l_instInhabitedBool;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRefl_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_instMonadTraceOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_instMonadLiftT(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_x27_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkProjection_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instMonadOptionsOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_withTraceNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwAppTypeMismatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAbsurd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_congrArg_x3f___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_congrArg_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkExpectedTypeHintCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_congrArg_x3f___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_mkProjection___lam__1(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrFun___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_8430_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadAlwaysExceptEIO(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkProjection_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRefl_x3f___boxed(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadLift(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkProjection_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_congrArg_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_congrArg_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_instMonadLiftBaseIOEIO(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrFun___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_x27_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkProjection_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_11 = l_Lean_Meta_getLevel(x_9, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_mk_string_unchecked("id", 2, 2);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_16);
lean_ctor_set(x_7, 0, x_13);
x_17 = l_Lean_Expr_const___override(x_15, x_7);
x_18 = l_Lean_mkAppB(x_17, x_9, x_1);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_mk_string_unchecked("id", 2, 2);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_23);
lean_ctor_set(x_7, 0, x_19);
x_24 = l_Lean_Expr_const___override(x_22, x_7);
x_25 = l_Lean_mkAppB(x_24, x_9, x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
lean_inc(x_31);
x_33 = l_Lean_Meta_getLevel(x_31, x_2, x_3, x_4, x_5, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_37 = lean_mk_string_unchecked("id", 2, 2);
x_38 = l_Lean_Name_mkStr1(x_37);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Expr_const___override(x_38, x_40);
x_42 = l_Lean_mkAppB(x_41, x_31, x_1);
if (lean_is_scalar(x_36)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_36;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_35);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_31);
lean_dec(x_1);
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_46 = x_33;
} else {
 lean_dec_ref(x_33);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkExpectedTypeHintCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_mk_string_unchecked("id", 2, 2);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_Expr_const___override(x_5, x_7);
x_9 = l_Lean_mkAppB(x_8, x_2, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_Meta_mkExpectedTypeHintCore(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_2);
x_8 = l_Lean_Meta_getLevel(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Meta_mkExpectedTypeHintCore(x_1, x_2, x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = l_Lean_Meta_mkExpectedTypeHintCore(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetFun___lam__0(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
return x_1;
}
case 8:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
x_7 = l_Lean_Expr_lam___override(x_2, x_3, x_4, x_6);
return x_7;
}
default: 
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_8 = lean_mk_string_unchecked("Lean.Meta.AppBuilder", 20, 20);
x_9 = lean_mk_string_unchecked("Lean.Meta.mkLetFun", 18, 18);
x_10 = lean_unsigned_to_nat(45u);
x_11 = lean_unsigned_to_nat(25u);
x_12 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_13 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_14 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; lean_object* x_86; 
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_mk_empty_array_with_capacity(x_58);
lean_inc(x_1);
x_60 = lean_array_push(x_59, x_1);
x_61 = lean_box(0);
x_62 = lean_box(1);
x_82 = lean_unbox(x_61);
x_83 = lean_unbox(x_61);
x_84 = lean_unbox(x_61);
x_85 = lean_unbox(x_62);
lean_inc(x_3);
x_86 = l_Lean_Meta_mkLambdaFVars(x_60, x_3, x_82, x_83, x_84, x_85, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Meta_mkLetFun___lam__0(x_87);
x_63 = x_89;
x_64 = x_88;
goto block_81;
}
else
{
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_86, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_dec(x_86);
x_63 = x_90;
x_64 = x_91;
goto block_81;
}
else
{
lean_dec(x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_86;
}
}
block_57:
{
lean_object* x_14; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_11);
x_14 = l_Lean_Meta_getLevel(x_11, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_getLevel(x_9, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_mk_string_unchecked("letFun", 6, 6);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Expr_const___override(x_21, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = lean_mk_empty_array_with_capacity(x_26);
x_28 = lean_array_push(x_27, x_11);
x_29 = lean_array_push(x_28, x_12);
x_30 = lean_array_push(x_29, x_2);
x_31 = lean_array_push(x_30, x_10);
x_32 = l_Lean_mkAppN(x_25, x_31);
lean_dec(x_31);
lean_ctor_set(x_17, 0, x_32);
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
x_35 = lean_mk_string_unchecked("letFun", 6, 6);
x_36 = l_Lean_Name_mkStr1(x_35);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_15);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Expr_const___override(x_36, x_39);
x_41 = lean_unsigned_to_nat(4u);
x_42 = lean_mk_empty_array_with_capacity(x_41);
x_43 = lean_array_push(x_42, x_11);
x_44 = lean_array_push(x_43, x_12);
x_45 = lean_array_push(x_44, x_2);
x_46 = lean_array_push(x_45, x_10);
x_47 = l_Lean_mkAppN(x_40, x_46);
lean_dec(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_34);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_17);
if (x_49 == 0)
{
return x_17;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_17, 0);
x_51 = lean_ctor_get(x_17, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_17);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_14);
if (x_53 == 0)
{
return x_14;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_14, 0);
x_55 = lean_ctor_get(x_14, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_14);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
block_81:
{
lean_object* x_65; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_65 = lean_infer_type(x_3, x_4, x_5, x_6, x_7, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_68 = lean_infer_type(x_1, x_4, x_5, x_6, x_7, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_unbox(x_61);
x_72 = lean_unbox(x_61);
x_73 = lean_unbox(x_61);
x_74 = lean_unbox(x_62);
lean_inc(x_66);
x_75 = l_Lean_Meta_mkLambdaFVars(x_60, x_66, x_71, x_72, x_73, x_74, x_4, x_5, x_6, x_7, x_70);
lean_dec(x_60);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Meta_mkLetFun___lam__0(x_76);
x_9 = x_66;
x_10 = x_63;
x_11 = x_69;
x_12 = x_78;
x_13 = x_77;
goto block_57;
}
else
{
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
lean_dec(x_75);
x_9 = x_66;
x_10 = x_63;
x_11 = x_69;
x_12 = x_79;
x_13 = x_80;
goto block_57;
}
else
{
lean_dec(x_69);
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_75;
}
}
}
else
{
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_68;
}
}
else
{
lean_dec(x_63);
lean_dec(x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_12 = l_Lean_Meta_getLevel(x_10, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_mk_string_unchecked("Eq", 2, 2);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_box(0);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 1, x_17);
lean_ctor_set(x_8, 0, x_14);
x_18 = l_Lean_Expr_const___override(x_16, x_8);
x_19 = l_Lean_mkApp3(x_18, x_10, x_1, x_2);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_mk_string_unchecked("Eq", 2, 2);
x_23 = l_Lean_Name_mkStr1(x_22);
x_24 = lean_box(0);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 1, x_24);
lean_ctor_set(x_8, 0, x_20);
x_25 = l_Lean_Expr_const___override(x_23, x_8);
x_26 = l_Lean_mkApp3(x_25, x_10, x_1, x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_free_object(x_8);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_8, 0);
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_8);
lean_inc(x_32);
x_34 = l_Lean_Meta_getLevel(x_32, x_3, x_4, x_5, x_6, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = lean_mk_string_unchecked("Eq", 2, 2);
x_39 = l_Lean_Name_mkStr1(x_38);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Expr_const___override(x_39, x_41);
x_43 = l_Lean_mkApp3(x_42, x_32, x_1, x_2);
if (lean_is_scalar(x_37)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_37;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_36);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_32);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_ctor_get(x_34, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_47 = x_34;
} else {
 lean_dec_ref(x_34);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_9);
x_15 = l_Lean_Meta_getLevel(x_9, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_mk_string_unchecked("HEq", 3, 3);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = lean_box(0);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_20);
lean_ctor_set(x_11, 0, x_17);
x_21 = l_Lean_Expr_const___override(x_19, x_11);
x_22 = l_Lean_mkApp4(x_21, x_9, x_1, x_13, x_2);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_mk_string_unchecked("HEq", 3, 3);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_box(0);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_27);
lean_ctor_set(x_11, 0, x_23);
x_28 = l_Lean_Expr_const___override(x_26, x_11);
x_29 = l_Lean_mkApp4(x_28, x_9, x_1, x_13, x_2);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_11, 0);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_11);
lean_inc(x_9);
x_37 = l_Lean_Meta_getLevel(x_9, x_3, x_4, x_5, x_6, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_mk_string_unchecked("HEq", 3, 3);
x_42 = l_Lean_Name_mkStr1(x_41);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Expr_const___override(x_42, x_44);
x_46 = l_Lean_mkApp4(x_45, x_9, x_1, x_35, x_2);
if (lean_is_scalar(x_40)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_40;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_39);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_35);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_ctor_get(x_37, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_50 = x_37;
} else {
 lean_dec_ref(x_37);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqHEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_15 = l_Lean_Meta_getLevel(x_9, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_9);
x_18 = l_Lean_Meta_isExprDefEq(x_9, x_13, x_3, x_4, x_5, x_6, x_17);
lean_dec(x_3);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_mk_string_unchecked("HEq", 3, 3);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_box(0);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_25);
lean_ctor_set(x_11, 0, x_16);
x_26 = l_Lean_Expr_const___override(x_24, x_11);
x_27 = l_Lean_mkApp4(x_26, x_9, x_1, x_13, x_2);
lean_ctor_set(x_18, 0, x_27);
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_mk_string_unchecked("HEq", 3, 3);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = lean_box(0);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_31);
lean_ctor_set(x_11, 0, x_16);
x_32 = l_Lean_Expr_const___override(x_30, x_11);
x_33 = l_Lean_mkApp4(x_32, x_9, x_1, x_13, x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_13);
x_35 = !lean_is_exclusive(x_18);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_18, 0);
lean_dec(x_36);
x_37 = lean_mk_string_unchecked("Eq", 2, 2);
x_38 = l_Lean_Name_mkStr1(x_37);
x_39 = lean_box(0);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_39);
lean_ctor_set(x_11, 0, x_16);
x_40 = l_Lean_Expr_const___override(x_38, x_11);
x_41 = l_Lean_mkApp3(x_40, x_9, x_1, x_2);
lean_ctor_set(x_18, 0, x_41);
return x_18;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
lean_dec(x_18);
x_43 = lean_mk_string_unchecked("Eq", 2, 2);
x_44 = l_Lean_Name_mkStr1(x_43);
x_45 = lean_box(0);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_45);
lean_ctor_set(x_11, 0, x_16);
x_46 = l_Lean_Expr_const___override(x_44, x_11);
x_47 = l_Lean_mkApp3(x_46, x_9, x_1, x_2);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_16);
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_18);
if (x_49 == 0)
{
return x_18;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_18, 0);
x_51 = lean_ctor_get(x_18, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_18);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_15);
if (x_53 == 0)
{
return x_15;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_15, 0);
x_55 = lean_ctor_get(x_15, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_15);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_11, 0);
x_58 = lean_ctor_get(x_11, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_59 = l_Lean_Meta_getLevel(x_9, x_3, x_4, x_5, x_6, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_57);
lean_inc(x_9);
x_62 = l_Lean_Meta_isExprDefEq(x_9, x_57, x_3, x_4, x_5, x_6, x_61);
lean_dec(x_3);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_66 = x_62;
} else {
 lean_dec_ref(x_62);
 x_66 = lean_box(0);
}
x_67 = lean_mk_string_unchecked("HEq", 3, 3);
x_68 = l_Lean_Name_mkStr1(x_67);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_60);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_Expr_const___override(x_68, x_70);
x_72 = l_Lean_mkApp4(x_71, x_9, x_1, x_57, x_2);
if (lean_is_scalar(x_66)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_66;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_65);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_57);
x_74 = lean_ctor_get(x_62, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_75 = x_62;
} else {
 lean_dec_ref(x_62);
 x_75 = lean_box(0);
}
x_76 = lean_mk_string_unchecked("Eq", 2, 2);
x_77 = l_Lean_Name_mkStr1(x_76);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_60);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_Expr_const___override(x_77, x_79);
x_81 = l_Lean_mkApp3(x_80, x_9, x_1, x_2);
if (lean_is_scalar(x_75)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_75;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_74);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_83 = lean_ctor_get(x_62, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_62, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_85 = x_62;
} else {
 lean_dec_ref(x_62);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_57);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = lean_ctor_get(x_59, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_59, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_89 = x_59;
} else {
 lean_dec_ref(x_59);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRefl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_11 = l_Lean_Meta_getLevel(x_9, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_mk_string_unchecked("Eq", 2, 2);
x_15 = lean_mk_string_unchecked("refl", 4, 4);
x_16 = l_Lean_Name_mkStr2(x_14, x_15);
x_17 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_17);
lean_ctor_set(x_7, 0, x_13);
x_18 = l_Lean_Expr_const___override(x_16, x_7);
x_19 = l_Lean_mkAppB(x_18, x_9, x_1);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_mk_string_unchecked("Eq", 2, 2);
x_23 = lean_mk_string_unchecked("refl", 4, 4);
x_24 = l_Lean_Name_mkStr2(x_22, x_23);
x_25 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_20);
x_26 = l_Lean_Expr_const___override(x_24, x_7);
x_27 = l_Lean_mkAppB(x_26, x_9, x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_7, 0);
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_7);
lean_inc(x_33);
x_35 = l_Lean_Meta_getLevel(x_33, x_2, x_3, x_4, x_5, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_mk_string_unchecked("Eq", 2, 2);
x_40 = lean_mk_string_unchecked("refl", 4, 4);
x_41 = l_Lean_Name_mkStr2(x_39, x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Expr_const___override(x_41, x_43);
x_45 = l_Lean_mkAppB(x_44, x_33, x_1);
if (lean_is_scalar(x_38)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_38;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_37);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_33);
lean_dec(x_1);
x_47 = lean_ctor_get(x_35, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_35, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_49 = x_35;
} else {
 lean_dec_ref(x_35);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqRefl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_11 = l_Lean_Meta_getLevel(x_9, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_mk_string_unchecked("HEq", 3, 3);
x_15 = lean_mk_string_unchecked("refl", 4, 4);
x_16 = l_Lean_Name_mkStr2(x_14, x_15);
x_17 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_17);
lean_ctor_set(x_7, 0, x_13);
x_18 = l_Lean_Expr_const___override(x_16, x_7);
x_19 = l_Lean_mkAppB(x_18, x_9, x_1);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_mk_string_unchecked("HEq", 3, 3);
x_23 = lean_mk_string_unchecked("refl", 4, 4);
x_24 = l_Lean_Name_mkStr2(x_22, x_23);
x_25 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_20);
x_26 = l_Lean_Expr_const___override(x_24, x_7);
x_27 = l_Lean_mkAppB(x_26, x_9, x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_7, 0);
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_7);
lean_inc(x_33);
x_35 = l_Lean_Meta_getLevel(x_33, x_2, x_3, x_4, x_5, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_mk_string_unchecked("HEq", 3, 3);
x_40 = lean_mk_string_unchecked("refl", 4, 4);
x_41 = l_Lean_Name_mkStr2(x_39, x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Expr_const___override(x_41, x_43);
x_45 = l_Lean_mkAppB(x_44, x_33, x_1);
if (lean_is_scalar(x_38)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_38;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_37);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_33);
lean_dec(x_1);
x_47 = lean_ctor_get(x_35, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_35, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_49 = x_35;
} else {
 lean_dec_ref(x_35);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAbsurd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_9 = lean_infer_type(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_1);
x_13 = l_Lean_Meta_getLevel(x_1, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_mk_string_unchecked("absurd", 6, 6);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_box(0);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 1, x_18);
lean_ctor_set(x_9, 0, x_15);
x_19 = l_Lean_Expr_const___override(x_17, x_9);
x_20 = l_Lean_mkApp4(x_19, x_11, x_1, x_2, x_3);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_mk_string_unchecked("absurd", 6, 6);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_box(0);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 1, x_25);
lean_ctor_set(x_9, 0, x_21);
x_26 = l_Lean_Expr_const___override(x_24, x_9);
x_27 = l_Lean_mkApp4(x_26, x_11, x_1, x_2, x_3);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_free_object(x_9);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_9, 0);
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_9);
lean_inc(x_1);
x_35 = l_Lean_Meta_getLevel(x_1, x_4, x_5, x_6, x_7, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_mk_string_unchecked("absurd", 6, 6);
x_40 = l_Lean_Name_mkStr1(x_39);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Expr_const___override(x_40, x_42);
x_44 = l_Lean_mkApp4(x_43, x_33, x_1, x_2, x_3);
if (lean_is_scalar(x_38)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_38;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_37);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_33);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_ctor_get(x_35, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_35, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_48 = x_35;
} else {
 lean_dec_ref(x_35);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFalseElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Meta_getLevel(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_mk_string_unchecked("False", 5, 5);
x_12 = lean_mk_string_unchecked("elim", 4, 4);
x_13 = l_Lean_Name_mkStr2(x_11, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Expr_const___override(x_13, x_15);
x_17 = l_Lean_mkAppB(x_16, x_1, x_2);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_mk_string_unchecked("False", 5, 5);
x_21 = lean_mk_string_unchecked("elim", 4, 4);
x_22 = l_Lean_Name_mkStr2(x_20, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Expr_const___override(x_22, x_24);
x_26 = l_Lean_mkAppB(x_25, x_1, x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_8);
if (x_28 == 0)
{
return x_8;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_8, 0);
x_30 = lean_ctor_get(x_8, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_8);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_whnfD(x_8, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_2);
return x_10;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_mk_string_unchecked("", 0, 0);
x_4 = l_Lean_stringToMessageData(x_3);
lean_dec(x_3);
x_5 = l_Lean_indentExpr(x_1);
lean_inc(x_4);
x_6 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked("\nhas type", 9, 9);
x_8 = l_Lean_stringToMessageData(x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_indentExpr(x_2);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_mk_string_unchecked("AppBuilder for '", 16, 16);
x_9 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
x_10 = l_Lean_MessageData_ofName(x_1);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_mk_string_unchecked("', ", 3, 3);
x_13 = l_Lean_stringToMessageData(x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_mk_string_unchecked("", 0, 0);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_18, x_3, x_4, x_5, x_6, x_7);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqSymm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_mk_string_unchecked("Eq", 2, 2);
x_8 = lean_mk_string_unchecked("refl", 4, 4);
lean_inc(x_7);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = l_Lean_Expr_isAppOf(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_7);
x_15 = l_Lean_Name_mkStr1(x_7);
x_16 = lean_unsigned_to_nat(3u);
x_17 = l_Lean_Expr_isAppOfArity(x_13, x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_mk_string_unchecked("symm", 4, 4);
x_19 = l_Lean_Name_mkStr2(x_7, x_18);
x_20 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_MessageData_ofFormat(x_21);
x_23 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_13);
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_23);
lean_ctor_set(x_11, 0, x_22);
x_24 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_19, x_11, x_2, x_3, x_4, x_5, x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = l_Lean_Expr_appFn_x21(x_13);
x_26 = l_Lean_Expr_appFn_x21(x_25);
x_27 = l_Lean_Expr_appArg_x21(x_26);
lean_dec(x_26);
lean_inc(x_27);
x_28 = l_Lean_Meta_getLevel(x_27, x_2, x_3, x_4, x_5, x_14);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = l_Lean_Expr_appArg_x21(x_25);
lean_dec(x_25);
x_32 = l_Lean_Expr_appArg_x21(x_13);
lean_dec(x_13);
x_33 = lean_mk_string_unchecked("symm", 4, 4);
x_34 = l_Lean_Name_mkStr2(x_7, x_33);
x_35 = lean_box(0);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_35);
lean_ctor_set(x_11, 0, x_30);
x_36 = l_Lean_Expr_const___override(x_34, x_11);
x_37 = l_Lean_mkApp4(x_36, x_27, x_31, x_32, x_1);
lean_ctor_set(x_28, 0, x_37);
return x_28;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_28, 0);
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_28);
x_40 = l_Lean_Expr_appArg_x21(x_25);
lean_dec(x_25);
x_41 = l_Lean_Expr_appArg_x21(x_13);
lean_dec(x_13);
x_42 = lean_mk_string_unchecked("symm", 4, 4);
x_43 = l_Lean_Name_mkStr2(x_7, x_42);
x_44 = lean_box(0);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_44);
lean_ctor_set(x_11, 0, x_38);
x_45 = l_Lean_Expr_const___override(x_43, x_11);
x_46 = l_Lean_mkApp4(x_45, x_27, x_40, x_41, x_1);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_39);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_27);
lean_dec(x_25);
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_28);
if (x_48 == 0)
{
return x_28;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_28, 0);
x_50 = lean_ctor_get(x_28, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_28);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_11, 0);
x_53 = lean_ctor_get(x_11, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_11);
lean_inc(x_7);
x_54 = l_Lean_Name_mkStr1(x_7);
x_55 = lean_unsigned_to_nat(3u);
x_56 = l_Lean_Expr_isAppOfArity(x_52, x_54, x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_mk_string_unchecked("symm", 4, 4);
x_58 = l_Lean_Name_mkStr2(x_7, x_57);
x_59 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = l_Lean_MessageData_ofFormat(x_60);
x_62 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_52);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_58, x_63, x_2, x_3, x_4, x_5, x_53);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = l_Lean_Expr_appFn_x21(x_52);
x_66 = l_Lean_Expr_appFn_x21(x_65);
x_67 = l_Lean_Expr_appArg_x21(x_66);
lean_dec(x_66);
lean_inc(x_67);
x_68 = l_Lean_Meta_getLevel(x_67, x_2, x_3, x_4, x_5, x_53);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = l_Lean_Expr_appArg_x21(x_65);
lean_dec(x_65);
x_73 = l_Lean_Expr_appArg_x21(x_52);
lean_dec(x_52);
x_74 = lean_mk_string_unchecked("symm", 4, 4);
x_75 = l_Lean_Name_mkStr2(x_7, x_74);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_69);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Expr_const___override(x_75, x_77);
x_79 = l_Lean_mkApp4(x_78, x_67, x_72, x_73, x_1);
if (lean_is_scalar(x_71)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_71;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_70);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_52);
lean_dec(x_7);
lean_dec(x_1);
x_81 = lean_ctor_get(x_68, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_68, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_83 = x_68;
} else {
 lean_dec_ref(x_68);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
else
{
lean_object* x_85; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_1);
lean_ctor_set(x_85, 1, x_6);
return x_85;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_mk_string_unchecked("Eq", 2, 2);
x_9 = lean_mk_string_unchecked("refl", 4, 4);
lean_inc(x_8);
x_10 = l_Lean_Name_mkStr2(x_8, x_9);
x_11 = l_Lean_Expr_isAppOf(x_1, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isAppOf(x_2, x_10);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_13 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_2, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_8);
x_20 = l_Lean_Name_mkStr1(x_8);
x_21 = lean_unsigned_to_nat(3u);
x_22 = l_Lean_Expr_isAppOfArity(x_14, x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_2);
x_23 = lean_mk_string_unchecked("trans", 5, 5);
x_24 = l_Lean_Name_mkStr2(x_8, x_23);
x_25 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_MessageData_ofFormat(x_26);
x_28 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_14);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_28);
lean_ctor_set(x_16, 0, x_27);
x_29 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_24, x_16, x_3, x_4, x_5, x_6, x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = l_Lean_Expr_isAppOfArity(x_18, x_20, x_21);
lean_dec(x_20);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_14);
lean_dec(x_1);
x_31 = lean_mk_string_unchecked("trans", 5, 5);
x_32 = l_Lean_Name_mkStr2(x_8, x_31);
x_33 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_MessageData_ofFormat(x_34);
x_36 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_18);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_36);
lean_ctor_set(x_16, 0, x_35);
x_37 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_32, x_16, x_3, x_4, x_5, x_6, x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = l_Lean_Expr_appFn_x21(x_14);
x_39 = l_Lean_Expr_appFn_x21(x_38);
x_40 = l_Lean_Expr_appArg_x21(x_39);
lean_dec(x_39);
lean_inc(x_40);
x_41 = l_Lean_Meta_getLevel(x_40, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = l_Lean_Expr_appArg_x21(x_38);
lean_dec(x_38);
x_45 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_46 = l_Lean_Expr_appArg_x21(x_18);
lean_dec(x_18);
x_47 = lean_mk_string_unchecked("trans", 5, 5);
x_48 = l_Lean_Name_mkStr2(x_8, x_47);
x_49 = lean_box(0);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_49);
lean_ctor_set(x_16, 0, x_43);
x_50 = l_Lean_Expr_const___override(x_48, x_16);
x_51 = l_Lean_mkApp6(x_50, x_40, x_44, x_45, x_46, x_1, x_2);
lean_ctor_set(x_41, 0, x_51);
return x_41;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_52 = lean_ctor_get(x_41, 0);
x_53 = lean_ctor_get(x_41, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_41);
x_54 = l_Lean_Expr_appArg_x21(x_38);
lean_dec(x_38);
x_55 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_56 = l_Lean_Expr_appArg_x21(x_18);
lean_dec(x_18);
x_57 = lean_mk_string_unchecked("trans", 5, 5);
x_58 = l_Lean_Name_mkStr2(x_8, x_57);
x_59 = lean_box(0);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_59);
lean_ctor_set(x_16, 0, x_52);
x_60 = l_Lean_Expr_const___override(x_58, x_16);
x_61 = l_Lean_mkApp6(x_60, x_40, x_54, x_55, x_56, x_1, x_2);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_53);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_40);
lean_dec(x_38);
lean_free_object(x_16);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_41);
if (x_63 == 0)
{
return x_41;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_41, 0);
x_65 = lean_ctor_get(x_41, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_41);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_ctor_get(x_16, 0);
x_68 = lean_ctor_get(x_16, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_16);
lean_inc(x_8);
x_69 = l_Lean_Name_mkStr1(x_8);
x_70 = lean_unsigned_to_nat(3u);
x_71 = l_Lean_Expr_isAppOfArity(x_14, x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_2);
x_72 = lean_mk_string_unchecked("trans", 5, 5);
x_73 = l_Lean_Name_mkStr2(x_8, x_72);
x_74 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = l_Lean_MessageData_ofFormat(x_75);
x_77 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_14);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_73, x_78, x_3, x_4, x_5, x_6, x_68);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_79;
}
else
{
uint8_t x_80; 
x_80 = l_Lean_Expr_isAppOfArity(x_67, x_69, x_70);
lean_dec(x_69);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_14);
lean_dec(x_1);
x_81 = lean_mk_string_unchecked("trans", 5, 5);
x_82 = l_Lean_Name_mkStr2(x_8, x_81);
x_83 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_84 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = l_Lean_MessageData_ofFormat(x_84);
x_86 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_67);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_82, x_87, x_3, x_4, x_5, x_6, x_68);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = l_Lean_Expr_appFn_x21(x_14);
x_90 = l_Lean_Expr_appFn_x21(x_89);
x_91 = l_Lean_Expr_appArg_x21(x_90);
lean_dec(x_90);
lean_inc(x_91);
x_92 = l_Lean_Meta_getLevel(x_91, x_3, x_4, x_5, x_6, x_68);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
x_96 = l_Lean_Expr_appArg_x21(x_89);
lean_dec(x_89);
x_97 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_98 = l_Lean_Expr_appArg_x21(x_67);
lean_dec(x_67);
x_99 = lean_mk_string_unchecked("trans", 5, 5);
x_100 = l_Lean_Name_mkStr2(x_8, x_99);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_93);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_Expr_const___override(x_100, x_102);
x_104 = l_Lean_mkApp6(x_103, x_91, x_96, x_97, x_98, x_1, x_2);
if (lean_is_scalar(x_95)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_95;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_94);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_67);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_106 = lean_ctor_get(x_92, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_92, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_108 = x_92;
} else {
 lean_dec_ref(x_92);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
else
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
else
{
lean_object* x_110; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_1);
lean_ctor_set(x_110, 1, x_7);
return x_110;
}
}
else
{
lean_object* x_111; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_2);
lean_ctor_set(x_111, 1, x_7);
return x_111;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_8 = x_14;
x_9 = x_7;
goto block_12;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_8 = x_15;
x_9 = x_7;
goto block_12;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = l_Lean_Meta_mkEqTrans(x_16, x_18, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_2, 0, x_21);
lean_ctor_set(x_19, 0, x_2);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_2, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_free_object(x_2);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
lean_dec(x_2);
x_30 = l_Lean_Meta_mkEqTrans(x_16, x_29, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_31);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqSymm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_mk_string_unchecked("HEq", 3, 3);
x_8 = lean_mk_string_unchecked("refl", 4, 4);
lean_inc(x_7);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = l_Lean_Expr_isAppOf(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_7);
x_15 = l_Lean_Name_mkStr1(x_7);
x_16 = lean_unsigned_to_nat(4u);
x_17 = l_Lean_Expr_isAppOfArity(x_13, x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_mk_string_unchecked("symm", 4, 4);
x_19 = l_Lean_Name_mkStr2(x_7, x_18);
x_20 = lean_mk_string_unchecked("heterogeneous equality proof expected", 37, 37);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_MessageData_ofFormat(x_21);
x_23 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_13);
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_23);
lean_ctor_set(x_11, 0, x_22);
x_24 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_19, x_11, x_2, x_3, x_4, x_5, x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = l_Lean_Expr_appFn_x21(x_13);
x_26 = l_Lean_Expr_appFn_x21(x_25);
x_27 = l_Lean_Expr_appFn_x21(x_26);
x_28 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
lean_inc(x_28);
x_29 = l_Lean_Meta_getLevel(x_28, x_2, x_3, x_4, x_5, x_14);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = l_Lean_Expr_appArg_x21(x_26);
lean_dec(x_26);
x_33 = l_Lean_Expr_appArg_x21(x_25);
lean_dec(x_25);
x_34 = l_Lean_Expr_appArg_x21(x_13);
lean_dec(x_13);
x_35 = lean_mk_string_unchecked("symm", 4, 4);
x_36 = l_Lean_Name_mkStr2(x_7, x_35);
x_37 = lean_box(0);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_37);
lean_ctor_set(x_11, 0, x_31);
x_38 = l_Lean_Expr_const___override(x_36, x_11);
x_39 = l_Lean_mkApp5(x_38, x_28, x_33, x_32, x_34, x_1);
lean_ctor_set(x_29, 0, x_39);
return x_29;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_29, 0);
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_29);
x_42 = l_Lean_Expr_appArg_x21(x_26);
lean_dec(x_26);
x_43 = l_Lean_Expr_appArg_x21(x_25);
lean_dec(x_25);
x_44 = l_Lean_Expr_appArg_x21(x_13);
lean_dec(x_13);
x_45 = lean_mk_string_unchecked("symm", 4, 4);
x_46 = l_Lean_Name_mkStr2(x_7, x_45);
x_47 = lean_box(0);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_47);
lean_ctor_set(x_11, 0, x_40);
x_48 = l_Lean_Expr_const___override(x_46, x_11);
x_49 = l_Lean_mkApp5(x_48, x_28, x_43, x_42, x_44, x_1);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_29);
if (x_51 == 0)
{
return x_29;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_29, 0);
x_53 = lean_ctor_get(x_29, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_29);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_11, 0);
x_56 = lean_ctor_get(x_11, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_11);
lean_inc(x_7);
x_57 = l_Lean_Name_mkStr1(x_7);
x_58 = lean_unsigned_to_nat(4u);
x_59 = l_Lean_Expr_isAppOfArity(x_55, x_57, x_58);
lean_dec(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_mk_string_unchecked("symm", 4, 4);
x_61 = l_Lean_Name_mkStr2(x_7, x_60);
x_62 = lean_mk_string_unchecked("heterogeneous equality proof expected", 37, 37);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = l_Lean_MessageData_ofFormat(x_63);
x_65 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_55);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_61, x_66, x_2, x_3, x_4, x_5, x_56);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = l_Lean_Expr_appFn_x21(x_55);
x_69 = l_Lean_Expr_appFn_x21(x_68);
x_70 = l_Lean_Expr_appFn_x21(x_69);
x_71 = l_Lean_Expr_appArg_x21(x_70);
lean_dec(x_70);
lean_inc(x_71);
x_72 = l_Lean_Meta_getLevel(x_71, x_2, x_3, x_4, x_5, x_56);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
x_76 = l_Lean_Expr_appArg_x21(x_69);
lean_dec(x_69);
x_77 = l_Lean_Expr_appArg_x21(x_68);
lean_dec(x_68);
x_78 = l_Lean_Expr_appArg_x21(x_55);
lean_dec(x_55);
x_79 = lean_mk_string_unchecked("symm", 4, 4);
x_80 = l_Lean_Name_mkStr2(x_7, x_79);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_73);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_Expr_const___override(x_80, x_82);
x_84 = l_Lean_mkApp5(x_83, x_71, x_77, x_76, x_78, x_1);
if (lean_is_scalar(x_75)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_75;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_74);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_55);
lean_dec(x_7);
lean_dec(x_1);
x_86 = lean_ctor_get(x_72, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_72, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_88 = x_72;
} else {
 lean_dec_ref(x_72);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
else
{
lean_object* x_90; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_1);
lean_ctor_set(x_90, 1, x_6);
return x_90;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_mk_string_unchecked("HEq", 3, 3);
x_9 = lean_mk_string_unchecked("refl", 4, 4);
lean_inc(x_8);
x_10 = l_Lean_Name_mkStr2(x_8, x_9);
x_11 = l_Lean_Expr_isAppOf(x_1, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isAppOf(x_2, x_10);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_13 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_2, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_8);
x_20 = l_Lean_Name_mkStr1(x_8);
x_21 = lean_unsigned_to_nat(4u);
x_22 = l_Lean_Expr_isAppOfArity(x_14, x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_2);
x_23 = lean_mk_string_unchecked("trans", 5, 5);
x_24 = l_Lean_Name_mkStr2(x_8, x_23);
x_25 = lean_mk_string_unchecked("heterogeneous equality proof expected", 37, 37);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_MessageData_ofFormat(x_26);
x_28 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_14);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_28);
lean_ctor_set(x_16, 0, x_27);
x_29 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_24, x_16, x_3, x_4, x_5, x_6, x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = l_Lean_Expr_isAppOfArity(x_18, x_20, x_21);
lean_dec(x_20);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_14);
lean_dec(x_1);
x_31 = lean_mk_string_unchecked("trans", 5, 5);
x_32 = l_Lean_Name_mkStr2(x_8, x_31);
x_33 = lean_mk_string_unchecked("heterogeneous equality proof expected", 37, 37);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_MessageData_ofFormat(x_34);
x_36 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_18);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_36);
lean_ctor_set(x_16, 0, x_35);
x_37 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_32, x_16, x_3, x_4, x_5, x_6, x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = l_Lean_Expr_appFn_x21(x_14);
x_39 = l_Lean_Expr_appFn_x21(x_38);
x_40 = l_Lean_Expr_appFn_x21(x_39);
x_41 = l_Lean_Expr_appArg_x21(x_40);
lean_dec(x_40);
lean_inc(x_41);
x_42 = l_Lean_Meta_getLevel(x_41, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = l_Lean_Expr_appFn_x21(x_18);
x_46 = l_Lean_Expr_appArg_x21(x_39);
lean_dec(x_39);
x_47 = l_Lean_Expr_appArg_x21(x_38);
lean_dec(x_38);
x_48 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_49 = l_Lean_Expr_appArg_x21(x_45);
lean_dec(x_45);
x_50 = l_Lean_Expr_appArg_x21(x_18);
lean_dec(x_18);
x_51 = lean_mk_string_unchecked("trans", 5, 5);
x_52 = l_Lean_Name_mkStr2(x_8, x_51);
x_53 = lean_box(0);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_53);
lean_ctor_set(x_16, 0, x_44);
x_54 = l_Lean_Expr_const___override(x_52, x_16);
x_55 = l_Lean_mkApp8(x_54, x_41, x_47, x_49, x_46, x_48, x_50, x_1, x_2);
lean_ctor_set(x_42, 0, x_55);
return x_42;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_56 = lean_ctor_get(x_42, 0);
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_42);
x_58 = l_Lean_Expr_appFn_x21(x_18);
x_59 = l_Lean_Expr_appArg_x21(x_39);
lean_dec(x_39);
x_60 = l_Lean_Expr_appArg_x21(x_38);
lean_dec(x_38);
x_61 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_62 = l_Lean_Expr_appArg_x21(x_58);
lean_dec(x_58);
x_63 = l_Lean_Expr_appArg_x21(x_18);
lean_dec(x_18);
x_64 = lean_mk_string_unchecked("trans", 5, 5);
x_65 = l_Lean_Name_mkStr2(x_8, x_64);
x_66 = lean_box(0);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_66);
lean_ctor_set(x_16, 0, x_56);
x_67 = l_Lean_Expr_const___override(x_65, x_16);
x_68 = l_Lean_mkApp8(x_67, x_41, x_60, x_62, x_59, x_61, x_63, x_1, x_2);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_57);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_38);
lean_free_object(x_16);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_42);
if (x_70 == 0)
{
return x_42;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_42, 0);
x_72 = lean_ctor_get(x_42, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_42);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = lean_ctor_get(x_16, 0);
x_75 = lean_ctor_get(x_16, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_16);
lean_inc(x_8);
x_76 = l_Lean_Name_mkStr1(x_8);
x_77 = lean_unsigned_to_nat(4u);
x_78 = l_Lean_Expr_isAppOfArity(x_14, x_76, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_76);
lean_dec(x_74);
lean_dec(x_2);
x_79 = lean_mk_string_unchecked("trans", 5, 5);
x_80 = l_Lean_Name_mkStr2(x_8, x_79);
x_81 = lean_mk_string_unchecked("heterogeneous equality proof expected", 37, 37);
x_82 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = l_Lean_MessageData_ofFormat(x_82);
x_84 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_14);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_80, x_85, x_3, x_4, x_5, x_6, x_75);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_86;
}
else
{
uint8_t x_87; 
x_87 = l_Lean_Expr_isAppOfArity(x_74, x_76, x_77);
lean_dec(x_76);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_14);
lean_dec(x_1);
x_88 = lean_mk_string_unchecked("trans", 5, 5);
x_89 = l_Lean_Name_mkStr2(x_8, x_88);
x_90 = lean_mk_string_unchecked("heterogeneous equality proof expected", 37, 37);
x_91 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = l_Lean_MessageData_ofFormat(x_91);
x_93 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_74);
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_89, x_94, x_3, x_4, x_5, x_6, x_75);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = l_Lean_Expr_appFn_x21(x_14);
x_97 = l_Lean_Expr_appFn_x21(x_96);
x_98 = l_Lean_Expr_appFn_x21(x_97);
x_99 = l_Lean_Expr_appArg_x21(x_98);
lean_dec(x_98);
lean_inc(x_99);
x_100 = l_Lean_Meta_getLevel(x_99, x_3, x_4, x_5, x_6, x_75);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_104 = l_Lean_Expr_appFn_x21(x_74);
x_105 = l_Lean_Expr_appArg_x21(x_97);
lean_dec(x_97);
x_106 = l_Lean_Expr_appArg_x21(x_96);
lean_dec(x_96);
x_107 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_108 = l_Lean_Expr_appArg_x21(x_104);
lean_dec(x_104);
x_109 = l_Lean_Expr_appArg_x21(x_74);
lean_dec(x_74);
x_110 = lean_mk_string_unchecked("trans", 5, 5);
x_111 = l_Lean_Name_mkStr2(x_8, x_110);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_101);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_Expr_const___override(x_111, x_113);
x_115 = l_Lean_mkApp8(x_114, x_99, x_106, x_108, x_105, x_107, x_109, x_1, x_2);
if (lean_is_scalar(x_103)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_103;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_102);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_99);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_74);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_117 = lean_ctor_get(x_100, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_100, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_119 = x_100;
} else {
 lean_dec_ref(x_100);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
else
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
else
{
lean_object* x_121; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_1);
lean_ctor_set(x_121, 1, x_7);
return x_121;
}
}
else
{
lean_object* x_122; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_2);
lean_ctor_set(x_122, 1, x_7);
return x_122;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_12 = lean_mk_string_unchecked("HEq", 3, 3);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_unsigned_to_nat(4u);
x_15 = l_Lean_Expr_isAppOfArity(x_9, x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_9);
x_16 = lean_mk_string_unchecked("eq_of_heq", 9, 9);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_mk_string_unchecked("heterogeneous equality proof expected", 37, 37);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = l_Lean_indentExpr(x_1);
if (lean_is_scalar(x_11)) {
 x_21 = lean_alloc_ctor(7, 2, 0);
} else {
 x_21 = x_11;
 lean_ctor_set_tag(x_21, 7);
}
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked("", 0, 0);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_17, x_24, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_26 = l_Lean_Expr_appFn_x21(x_9);
x_27 = l_Lean_Expr_appFn_x21(x_26);
x_28 = l_Lean_Expr_appFn_x21(x_27);
x_29 = l_Lean_Expr_appArg_x21(x_28);
lean_dec(x_28);
x_30 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
x_31 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
if (x_2 == 0)
{
lean_dec(x_26);
x_32 = x_3;
x_33 = x_4;
x_34 = x_5;
x_35 = x_6;
x_36 = x_10;
goto block_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Lean_Expr_appArg_x21(x_26);
lean_dec(x_26);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_60);
lean_inc(x_29);
x_61 = l_Lean_Meta_isExprDefEq(x_29, x_60, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_11);
lean_dec(x_1);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_mk_string_unchecked("eq_of_heq", 9, 9);
x_66 = l_Lean_Name_mkStr1(x_65);
x_67 = lean_mk_string_unchecked("heterogeneous equality types are not definitionally equal", 57, 57);
x_68 = l_Lean_stringToMessageData(x_67);
lean_dec(x_67);
x_69 = l_Lean_indentExpr(x_29);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_mk_string_unchecked("\nis not definitionally equal to", 31, 31);
x_72 = l_Lean_stringToMessageData(x_71);
lean_dec(x_71);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_indentExpr(x_60);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_mk_string_unchecked("", 0, 0);
x_77 = l_Lean_stringToMessageData(x_76);
lean_dec(x_76);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
x_79 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_66, x_78, x_3, x_4, x_5, x_6, x_64);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
return x_79;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_79);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_60);
x_84 = lean_ctor_get(x_61, 1);
lean_inc(x_84);
lean_dec(x_61);
x_32 = x_3;
x_33 = x_4;
x_34 = x_5;
x_35 = x_6;
x_36 = x_84;
goto block_59;
}
}
else
{
uint8_t x_85; 
lean_dec(x_60);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_61);
if (x_85 == 0)
{
return x_61;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_61, 0);
x_87 = lean_ctor_get(x_61, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_61);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
block_59:
{
lean_object* x_37; 
lean_inc(x_29);
x_37 = l_Lean_Meta_getLevel(x_29, x_32, x_33, x_34, x_35, x_36);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_mk_string_unchecked("eq_of_heq", 9, 9);
x_41 = l_Lean_Name_mkStr1(x_40);
x_42 = lean_box(0);
if (lean_is_scalar(x_11)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_11;
 lean_ctor_set_tag(x_43, 1);
}
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Expr_const___override(x_41, x_43);
x_45 = l_Lean_mkApp4(x_44, x_29, x_30, x_31, x_1);
lean_ctor_set(x_37, 0, x_45);
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_37, 0);
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_37);
x_48 = lean_mk_string_unchecked("eq_of_heq", 9, 9);
x_49 = l_Lean_Name_mkStr1(x_48);
x_50 = lean_box(0);
if (lean_is_scalar(x_11)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_11;
 lean_ctor_set_tag(x_51, 1);
}
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Expr_const___override(x_49, x_51);
x_53 = l_Lean_mkApp4(x_52, x_29, x_30, x_31, x_1);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_47);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_37);
if (x_55 == 0)
{
return x_37;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_37, 0);
x_57 = lean_ctor_get(x_37, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_37);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_mkEqOfHEq(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqOfEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_mk_string_unchecked("Eq", 2, 2);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Expr_isAppOfArity(x_9, x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
x_15 = lean_mk_string_unchecked("heq_of_eq", 9, 9);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_7, 7);
lean_ctor_set(x_7, 1, x_19);
lean_ctor_set(x_7, 0, x_18);
x_20 = lean_mk_string_unchecked("", 0, 0);
x_21 = l_Lean_stringToMessageData(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_21);
x_23 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_16, x_22, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = l_Lean_Expr_appFn_x21(x_9);
x_25 = l_Lean_Expr_appFn_x21(x_24);
x_26 = l_Lean_Expr_appArg_x21(x_25);
lean_dec(x_25);
lean_inc(x_26);
x_27 = l_Lean_Meta_getLevel(x_26, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = l_Lean_Expr_appArg_x21(x_24);
lean_dec(x_24);
x_31 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
x_32 = lean_mk_string_unchecked("heq_of_eq", 9, 9);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_34);
lean_ctor_set(x_7, 0, x_29);
x_35 = l_Lean_Expr_const___override(x_33, x_7);
x_36 = l_Lean_mkApp4(x_35, x_26, x_30, x_31, x_1);
lean_ctor_set(x_27, 0, x_36);
return x_27;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_27, 0);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_27);
x_39 = l_Lean_Expr_appArg_x21(x_24);
lean_dec(x_24);
x_40 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
x_41 = lean_mk_string_unchecked("heq_of_eq", 9, 9);
x_42 = l_Lean_Name_mkStr1(x_41);
x_43 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_43);
lean_ctor_set(x_7, 0, x_37);
x_44 = l_Lean_Expr_const___override(x_42, x_7);
x_45 = l_Lean_mkApp4(x_44, x_26, x_39, x_40, x_1);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_38);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_26);
lean_dec(x_24);
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_27);
if (x_47 == 0)
{
return x_27;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_27, 0);
x_49 = lean_ctor_get(x_27, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_27);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_7, 0);
x_52 = lean_ctor_get(x_7, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_7);
x_53 = lean_mk_string_unchecked("Eq", 2, 2);
x_54 = l_Lean_Name_mkStr1(x_53);
x_55 = lean_unsigned_to_nat(3u);
x_56 = l_Lean_Expr_isAppOfArity(x_51, x_54, x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_51);
x_57 = lean_mk_string_unchecked("heq_of_eq", 9, 9);
x_58 = l_Lean_Name_mkStr1(x_57);
x_59 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_60 = l_Lean_stringToMessageData(x_59);
lean_dec(x_59);
x_61 = l_Lean_indentExpr(x_1);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_mk_string_unchecked("", 0, 0);
x_64 = l_Lean_stringToMessageData(x_63);
lean_dec(x_63);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
x_66 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_58, x_65, x_2, x_3, x_4, x_5, x_52);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = l_Lean_Expr_appFn_x21(x_51);
x_68 = l_Lean_Expr_appFn_x21(x_67);
x_69 = l_Lean_Expr_appArg_x21(x_68);
lean_dec(x_68);
lean_inc(x_69);
x_70 = l_Lean_Meta_getLevel(x_69, x_2, x_3, x_4, x_5, x_52);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = l_Lean_Expr_appArg_x21(x_67);
lean_dec(x_67);
x_75 = l_Lean_Expr_appArg_x21(x_51);
lean_dec(x_51);
x_76 = lean_mk_string_unchecked("heq_of_eq", 9, 9);
x_77 = l_Lean_Name_mkStr1(x_76);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_71);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_Expr_const___override(x_77, x_79);
x_81 = l_Lean_mkApp4(x_80, x_69, x_74, x_75, x_1);
if (lean_is_scalar(x_73)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_73;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_72);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_51);
lean_dec(x_1);
x_83 = lean_ctor_get(x_70, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_70, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_85 = x_70;
} else {
 lean_dec_ref(x_70);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRefl_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_mk_string_unchecked("Eq", 2, 2);
x_3 = lean_mk_string_unchecked("refl", 4, 4);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Expr_isAppOfArity(x_1, x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Expr_appArg_x21(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRefl_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_isRefl_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_congrArg_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___lam__0___boxed), 5, 0);
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_congrArg_x3f___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_10 = lean_mk_empty_array_with_capacity(x_1);
x_11 = lean_array_push(x_10, x_4);
lean_inc(x_11);
x_12 = l_Lean_Expr_beta(x_2, x_11);
x_13 = lean_box(0);
x_14 = lean_box(1);
x_15 = lean_unbox(x_13);
x_16 = lean_unbox(x_14);
x_17 = l_Lean_Meta_mkForallFVars(x_11, x_12, x_15, x_3, x_16, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_11);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_congrArg_x3f___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_10 = lean_mk_empty_array_with_capacity(x_1);
lean_inc(x_4);
x_11 = lean_array_push(x_10, x_4);
x_12 = l_Lean_Expr_app___override(x_4, x_2);
x_13 = lean_box(0);
x_14 = lean_box(1);
x_15 = lean_unbox(x_13);
x_16 = lean_unbox(x_13);
x_17 = lean_unbox(x_14);
x_18 = l_Lean_Meta_mkLambdaFVars(x_11, x_12, x_15, x_3, x_16, x_17, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_11);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_congrArg_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_mk_string_unchecked("congrArg", 8, 8);
x_87 = l_Lean_Name_mkStr1(x_86);
x_88 = lean_unsigned_to_nat(6u);
x_89 = l_Lean_Expr_isAppOfArity(x_1, x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
goto block_85;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_90 = lean_box(0);
x_91 = l_Lean_Expr_sort___override(x_90);
x_92 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_92);
x_93 = lean_mk_array(x_92, x_91);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_sub(x_92, x_94);
lean_dec(x_92);
lean_inc(x_1);
x_96 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_93, x_95);
x_97 = lean_array_get_size(x_96);
x_98 = lean_nat_dec_eq(x_97, x_88);
lean_dec(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_96);
x_99 = lean_mk_string_unchecked("Lean.Meta.AppBuilder", 20, 20);
x_100 = lean_mk_string_unchecked("Lean.Meta.congrArg\?", 19, 19);
x_101 = lean_unsigned_to_nat(216u);
x_102 = lean_unsigned_to_nat(49u);
x_103 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_104 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_99, x_100, x_101, x_102, x_103);
lean_dec(x_103);
lean_dec(x_100);
lean_dec(x_99);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_105 = l_panic___at___Lean_Meta_congrArg_x3f_spec__0(x_104, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_106;
goto block_85;
}
else
{
uint8_t x_107; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_105);
if (x_107 == 0)
{
return x_105;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_105, 0);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_105);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_111 = lean_unsigned_to_nat(0u);
x_112 = lean_array_fget(x_96, x_111);
x_113 = lean_unsigned_to_nat(4u);
x_114 = lean_array_fget(x_96, x_113);
x_115 = lean_unsigned_to_nat(5u);
x_116 = lean_array_fget(x_96, x_115);
lean_dec(x_96);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_112);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_6);
return x_120;
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
block_85:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_mk_string_unchecked("congrFun", 8, 8);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_unsigned_to_nat(6u);
x_19 = l_Lean_Expr_isAppOfArity(x_1, x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_7 = x_15;
goto block_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_box(0);
x_21 = l_Lean_Expr_sort___override(x_20);
x_22 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_22);
x_23 = lean_mk_array(x_22, x_21);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_22, x_24);
lean_dec(x_22);
x_26 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_23, x_25);
x_27 = lean_array_get_size(x_26);
x_28 = lean_nat_dec_eq(x_27, x_18);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_26);
x_29 = lean_mk_string_unchecked("Lean.Meta.AppBuilder", 20, 20);
x_30 = lean_mk_string_unchecked("Lean.Meta.congrArg\?", 19, 19);
x_31 = lean_unsigned_to_nat(219u);
x_32 = lean_unsigned_to_nat(48u);
x_33 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_34 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_29, x_30, x_31, x_32, x_33);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
x_35 = l_panic___at___Lean_Meta_congrArg_x3f_spec__0(x_34, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_7 = x_36;
goto block_10;
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_35);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; 
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_array_fget(x_26, x_41);
x_43 = lean_array_fget(x_26, x_24);
x_44 = lean_box(x_19);
x_45 = lean_alloc_closure((void*)(l_Lean_Meta_congrArg_x3f___lam__0___boxed), 9, 3);
lean_closure_set(x_45, 0, x_24);
lean_closure_set(x_45, 1, x_43);
lean_closure_set(x_45, 2, x_44);
x_46 = lean_mk_string_unchecked("x", 1, 1);
x_47 = l_Lean_Name_mkStr1(x_46);
x_48 = lean_box(0);
x_49 = lean_box(0);
x_50 = lean_unbox(x_48);
x_51 = lean_unbox(x_49);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_47);
x_52 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___redArg(x_47, x_50, x_42, x_45, x_51, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_unsigned_to_nat(5u);
x_56 = lean_array_fget(x_26, x_55);
x_57 = lean_box(x_19);
x_58 = lean_alloc_closure((void*)(l_Lean_Meta_congrArg_x3f___lam__1___boxed), 9, 3);
lean_closure_set(x_58, 0, x_24);
lean_closure_set(x_58, 1, x_56);
lean_closure_set(x_58, 2, x_57);
x_59 = lean_unbox(x_48);
x_60 = lean_unbox(x_49);
lean_inc(x_53);
x_61 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___redArg(x_47, x_59, x_53, x_58, x_60, x_11, x_12, x_13, x_14, x_54);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_unsigned_to_nat(4u);
x_65 = lean_array_fget(x_26, x_64);
lean_dec(x_26);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_53);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_61, 0, x_68);
return x_61;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_61, 0);
x_70 = lean_ctor_get(x_61, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_61);
x_71 = lean_unsigned_to_nat(4u);
x_72 = lean_array_fget(x_26, x_71);
lean_dec(x_26);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_53);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_70);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_53);
lean_dec(x_26);
x_77 = !lean_is_exclusive(x_61);
if (x_77 == 0)
{
return x_61;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_61, 0);
x_79 = lean_ctor_get(x_61, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_61);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_47);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_81 = !lean_is_exclusive(x_52);
if (x_81 == 0)
{
return x_52;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_52, 0);
x_83 = lean_ctor_get(x_52, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_52);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_congrArg_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_congrArg_x3f___lam__0(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_congrArg_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_congrArg_x3f___lam__1(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
lean_inc(x_10);
x_11 = lean_array_push(x_10, x_3);
lean_inc(x_11);
x_12 = l_Lean_Expr_beta(x_1, x_11);
x_13 = lean_array_push(x_10, x_12);
x_14 = l_Lean_Expr_beta(x_2, x_13);
x_15 = lean_box(0);
x_16 = lean_box(1);
x_17 = lean_box(1);
x_18 = lean_unbox(x_15);
x_19 = lean_unbox(x_16);
x_20 = lean_unbox(x_15);
x_21 = lean_unbox(x_17);
x_22 = l_Lean_Meta_mkLambdaFVars(x_11, x_14, x_18, x_19, x_20, x_21, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isRefl_x3f(x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Meta_congrArg_x3f(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_2, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_16 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
if (lean_obj_tag(x_17) == 7)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_17, 2);
lean_inc(x_30);
x_31 = l_Lean_Expr_hasLooseBVars(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_19);
lean_dec(x_17);
x_32 = lean_mk_string_unchecked("Eq", 2, 2);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = lean_unsigned_to_nat(3u);
x_35 = l_Lean_Expr_isAppOfArity(x_14, x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_1);
x_36 = lean_mk_string_unchecked("congrArg", 8, 8);
x_37 = l_Lean_Name_mkStr1(x_36);
x_38 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_Lean_MessageData_ofFormat(x_39);
x_41 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_14);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_41);
lean_ctor_set(x_12, 0, x_40);
x_42 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_37, x_12, x_3, x_4, x_5, x_6, x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_42;
}
else
{
lean_object* x_43; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_29);
x_43 = l_Lean_Meta_getLevel(x_29, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_30);
x_46 = l_Lean_Meta_getLevel(x_30, x_3, x_4, x_5, x_6, x_45);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = l_Lean_Expr_appFn_x21(x_14);
x_50 = l_Lean_Expr_appArg_x21(x_49);
lean_dec(x_49);
x_51 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_52 = lean_mk_string_unchecked("congrArg", 8, 8);
x_53 = l_Lean_Name_mkStr1(x_52);
x_54 = lean_box(0);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_54);
lean_ctor_set(x_12, 0, x_48);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_44);
lean_ctor_set(x_55, 1, x_12);
x_56 = l_Lean_Expr_const___override(x_53, x_55);
x_57 = l_Lean_mkApp6(x_56, x_29, x_30, x_50, x_51, x_1, x_2);
lean_ctor_set(x_46, 0, x_57);
return x_46;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_58 = lean_ctor_get(x_46, 0);
x_59 = lean_ctor_get(x_46, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_46);
x_60 = l_Lean_Expr_appFn_x21(x_14);
x_61 = l_Lean_Expr_appArg_x21(x_60);
lean_dec(x_60);
x_62 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_63 = lean_mk_string_unchecked("congrArg", 8, 8);
x_64 = l_Lean_Name_mkStr1(x_63);
x_65 = lean_box(0);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_65);
lean_ctor_set(x_12, 0, x_58);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_44);
lean_ctor_set(x_66, 1, x_12);
x_67 = l_Lean_Expr_const___override(x_64, x_66);
x_68 = l_Lean_mkApp6(x_67, x_29, x_30, x_61, x_62, x_1, x_2);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_59);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_44);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_12);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_46);
if (x_70 == 0)
{
return x_46;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_46, 0);
x_72 = lean_ctor_get(x_46, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_46);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_12);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_43);
if (x_74 == 0)
{
return x_43;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_43, 0);
x_76 = lean_ctor_get(x_43, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_43);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
else
{
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_12);
lean_dec(x_14);
lean_dec(x_2);
goto block_28;
}
}
else
{
lean_free_object(x_12);
lean_dec(x_14);
lean_dec(x_2);
goto block_28;
}
block_28:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_mk_string_unchecked("congrArg", 8, 8);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_mk_string_unchecked("non-dependent function expected", 31, 31);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_MessageData_ofFormat(x_23);
x_25 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_17);
if (lean_is_scalar(x_19)) {
 x_26 = lean_alloc_ctor(7, 2, 0);
} else {
 x_26 = x_19;
 lean_ctor_set_tag(x_26, 7);
}
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_21, x_26, x_3, x_4, x_5, x_6, x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_27;
}
}
else
{
lean_free_object(x_12);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_12, 0);
x_79 = lean_ctor_get(x_12, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_80 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_3, x_4, x_5, x_6, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
if (lean_obj_tag(x_81) == 7)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_81, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_81, 2);
lean_inc(x_94);
x_95 = l_Lean_Expr_hasLooseBVars(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
lean_dec(x_83);
lean_dec(x_81);
x_96 = lean_mk_string_unchecked("Eq", 2, 2);
x_97 = l_Lean_Name_mkStr1(x_96);
x_98 = lean_unsigned_to_nat(3u);
x_99 = l_Lean_Expr_isAppOfArity(x_78, x_97, x_98);
lean_dec(x_97);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_1);
x_100 = lean_mk_string_unchecked("congrArg", 8, 8);
x_101 = l_Lean_Name_mkStr1(x_100);
x_102 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_103 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = l_Lean_MessageData_ofFormat(x_103);
x_105 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_78);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_101, x_106, x_3, x_4, x_5, x_6, x_82);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_107;
}
else
{
lean_object* x_108; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_93);
x_108 = l_Lean_Meta_getLevel(x_93, x_3, x_4, x_5, x_6, x_82);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
lean_inc(x_94);
x_111 = l_Lean_Meta_getLevel(x_94, x_3, x_4, x_5, x_6, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
 x_114 = lean_box(0);
}
x_115 = l_Lean_Expr_appFn_x21(x_78);
x_116 = l_Lean_Expr_appArg_x21(x_115);
lean_dec(x_115);
x_117 = l_Lean_Expr_appArg_x21(x_78);
lean_dec(x_78);
x_118 = lean_mk_string_unchecked("congrArg", 8, 8);
x_119 = l_Lean_Name_mkStr1(x_118);
x_120 = lean_box(0);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_112);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_109);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_Expr_const___override(x_119, x_122);
x_124 = l_Lean_mkApp6(x_123, x_93, x_94, x_116, x_117, x_1, x_2);
if (lean_is_scalar(x_114)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_114;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_113);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_109);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_78);
lean_dec(x_2);
lean_dec(x_1);
x_126 = lean_ctor_get(x_111, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_111, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_128 = x_111;
} else {
 lean_dec_ref(x_111);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_78);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_130 = lean_ctor_get(x_108, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_108, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_132 = x_108;
} else {
 lean_dec_ref(x_108);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
}
else
{
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_78);
lean_dec(x_2);
goto block_92;
}
}
else
{
lean_dec(x_78);
lean_dec(x_2);
goto block_92;
}
block_92:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_84 = lean_mk_string_unchecked("congrArg", 8, 8);
x_85 = l_Lean_Name_mkStr1(x_84);
x_86 = lean_mk_string_unchecked("non-dependent function expected", 31, 31);
x_87 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = l_Lean_MessageData_ofFormat(x_87);
x_89 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_81);
if (lean_is_scalar(x_83)) {
 x_90 = lean_alloc_ctor(7, 2, 0);
} else {
 x_90 = x_83;
 lean_ctor_set_tag(x_90, 7);
}
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_85, x_90, x_3, x_4, x_5, x_6, x_82);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_91;
}
}
else
{
lean_dec(x_78);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_80;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; lean_object* x_147; 
lean_dec(x_2);
x_134 = lean_ctor_get(x_10, 0);
lean_inc(x_134);
lean_dec(x_10);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_9, 1);
lean_inc(x_136);
lean_dec(x_9);
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_135, 1);
lean_inc(x_139);
lean_dec(x_135);
x_140 = lean_alloc_closure((void*)(l_Lean_Meta_mkCongrArg___lam__0___boxed), 8, 2);
lean_closure_set(x_140, 0, x_138);
lean_closure_set(x_140, 1, x_1);
x_141 = lean_mk_string_unchecked("x", 1, 1);
x_142 = l_Lean_Name_mkStr1(x_141);
x_143 = lean_box(0);
x_144 = lean_box(0);
x_145 = lean_unbox(x_143);
x_146 = lean_unbox(x_144);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_147 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___redArg(x_142, x_145, x_137, x_140, x_146, x_3, x_4, x_5, x_6, x_136);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_1 = x_148;
x_2 = x_139;
x_7 = x_149;
goto _start;
}
else
{
lean_dec(x_139);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_147;
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_9);
if (x_151 == 0)
{
return x_9;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_9, 0);
x_153 = lean_ctor_get(x_9, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_9);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_2);
x_155 = lean_ctor_get(x_8, 0);
lean_inc(x_155);
lean_dec(x_8);
x_156 = l_Lean_Expr_app___override(x_1, x_155);
x_157 = l_Lean_Meta_mkEqRefl(x_156, x_3, x_4, x_5, x_6, x_7);
return x_157;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkCongrArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrFun___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
lean_inc(x_3);
x_11 = lean_array_push(x_10, x_3);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_14 = lean_array_push(x_13, x_3);
x_15 = lean_array_push(x_14, x_1);
x_16 = l_Lean_Expr_beta(x_2, x_15);
x_17 = lean_box(0);
x_18 = lean_box(1);
x_19 = lean_box(1);
x_20 = lean_unbox(x_17);
x_21 = lean_unbox(x_18);
x_22 = lean_unbox(x_17);
x_23 = lean_unbox(x_19);
x_24 = l_Lean_Meta_mkLambdaFVars(x_11, x_16, x_20, x_21, x_22, x_23, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isRefl_x3f(x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_9 = l_Lean_Meta_congrArg_x3f(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_mk_string_unchecked("Eq", 2, 2);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Expr_isAppOfArity(x_14, x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_20 = lean_mk_string_unchecked("congrFun", 8, 8);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_MessageData_ofFormat(x_23);
x_25 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_14);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_25);
lean_ctor_set(x_12, 0, x_24);
x_26 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_21, x_12, x_3, x_4, x_5, x_6, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l_Lean_Expr_appFn_x21(x_14);
x_28 = l_Lean_Expr_appFn_x21(x_27);
x_29 = l_Lean_Expr_appArg_x21(x_28);
lean_dec(x_28);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_30 = l_Lean_Meta_whnfD(x_29, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 7)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_30, 1);
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 2);
lean_inc(x_37);
lean_dec(x_31);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_36);
x_38 = l_Lean_Meta_getLevel(x_36, x_3, x_4, x_5, x_6, x_33);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_box(0);
x_42 = lean_unbox(x_41);
lean_inc(x_36);
x_43 = l_Lean_Expr_lam___override(x_35, x_36, x_37, x_42);
lean_inc(x_2);
lean_inc(x_43);
x_44 = l_Lean_Expr_app___override(x_43, x_2);
x_45 = l_Lean_Meta_getLevel(x_44, x_3, x_4, x_5, x_6, x_40);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
x_49 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_50 = lean_mk_string_unchecked("congrFun", 8, 8);
x_51 = l_Lean_Name_mkStr1(x_50);
x_52 = lean_box(0);
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 1, x_52);
lean_ctor_set(x_30, 0, x_47);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_30);
lean_ctor_set(x_12, 0, x_39);
x_53 = l_Lean_Expr_const___override(x_51, x_12);
x_54 = l_Lean_mkApp6(x_53, x_36, x_43, x_48, x_49, x_1, x_2);
lean_ctor_set(x_45, 0, x_54);
return x_45;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_55 = lean_ctor_get(x_45, 0);
x_56 = lean_ctor_get(x_45, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_45);
x_57 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
x_58 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_59 = lean_mk_string_unchecked("congrFun", 8, 8);
x_60 = l_Lean_Name_mkStr1(x_59);
x_61 = lean_box(0);
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 1, x_61);
lean_ctor_set(x_30, 0, x_55);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_30);
lean_ctor_set(x_12, 0, x_39);
x_62 = l_Lean_Expr_const___override(x_60, x_12);
x_63 = l_Lean_mkApp6(x_62, x_36, x_43, x_57, x_58, x_1, x_2);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_56);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_36);
lean_free_object(x_30);
lean_dec(x_27);
lean_free_object(x_12);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_45);
if (x_65 == 0)
{
return x_45;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_45, 0);
x_67 = lean_ctor_get(x_45, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_45);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_free_object(x_30);
lean_dec(x_27);
lean_free_object(x_12);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_38);
if (x_69 == 0)
{
return x_38;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_38, 0);
x_71 = lean_ctor_get(x_38, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_38);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_30, 1);
lean_inc(x_73);
lean_dec(x_30);
x_74 = lean_ctor_get(x_31, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_31, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_31, 2);
lean_inc(x_76);
lean_dec(x_31);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_75);
x_77 = l_Lean_Meta_getLevel(x_75, x_3, x_4, x_5, x_6, x_73);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_box(0);
x_81 = lean_unbox(x_80);
lean_inc(x_75);
x_82 = l_Lean_Expr_lam___override(x_74, x_75, x_76, x_81);
lean_inc(x_2);
lean_inc(x_82);
x_83 = l_Lean_Expr_app___override(x_82, x_2);
x_84 = l_Lean_Meta_getLevel(x_83, x_3, x_4, x_5, x_6, x_79);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
x_88 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
x_89 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_90 = lean_mk_string_unchecked("congrFun", 8, 8);
x_91 = l_Lean_Name_mkStr1(x_90);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_85);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_93);
lean_ctor_set(x_12, 0, x_78);
x_94 = l_Lean_Expr_const___override(x_91, x_12);
x_95 = l_Lean_mkApp6(x_94, x_75, x_82, x_88, x_89, x_1, x_2);
if (lean_is_scalar(x_87)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_87;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_86);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_82);
lean_dec(x_78);
lean_dec(x_75);
lean_dec(x_27);
lean_free_object(x_12);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_97 = lean_ctor_get(x_84, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_84, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_99 = x_84;
} else {
 lean_dec_ref(x_84);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_27);
lean_free_object(x_12);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = lean_ctor_get(x_77, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_77, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_103 = x_77;
} else {
 lean_dec_ref(x_77);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_31);
lean_dec(x_27);
lean_free_object(x_12);
lean_dec(x_2);
x_105 = !lean_is_exclusive(x_30);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_106 = lean_ctor_get(x_30, 1);
x_107 = lean_ctor_get(x_30, 0);
lean_dec(x_107);
x_108 = lean_mk_string_unchecked("congrFun", 8, 8);
x_109 = l_Lean_Name_mkStr1(x_108);
x_110 = lean_mk_string_unchecked("equality proof between functions expected", 41, 41);
x_111 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = l_Lean_MessageData_ofFormat(x_111);
x_113 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_14);
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_113);
lean_ctor_set(x_30, 0, x_112);
x_114 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_109, x_30, x_3, x_4, x_5, x_6, x_106);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_115 = lean_ctor_get(x_30, 1);
lean_inc(x_115);
lean_dec(x_30);
x_116 = lean_mk_string_unchecked("congrFun", 8, 8);
x_117 = l_Lean_Name_mkStr1(x_116);
x_118 = lean_mk_string_unchecked("equality proof between functions expected", 41, 41);
x_119 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = l_Lean_MessageData_ofFormat(x_119);
x_121 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_14);
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_117, x_122, x_3, x_4, x_5, x_6, x_115);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_123;
}
}
}
else
{
lean_dec(x_27);
lean_free_object(x_12);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_30;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_124 = lean_ctor_get(x_12, 0);
x_125 = lean_ctor_get(x_12, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_12);
x_126 = lean_mk_string_unchecked("Eq", 2, 2);
x_127 = l_Lean_Name_mkStr1(x_126);
x_128 = lean_unsigned_to_nat(3u);
x_129 = l_Lean_Expr_isAppOfArity(x_124, x_127, x_128);
lean_dec(x_127);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_2);
x_130 = lean_mk_string_unchecked("congrFun", 8, 8);
x_131 = l_Lean_Name_mkStr1(x_130);
x_132 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_133 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = l_Lean_MessageData_ofFormat(x_133);
x_135 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_124);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_131, x_136, x_3, x_4, x_5, x_6, x_125);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = l_Lean_Expr_appFn_x21(x_124);
x_139 = l_Lean_Expr_appFn_x21(x_138);
x_140 = l_Lean_Expr_appArg_x21(x_139);
lean_dec(x_139);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_141 = l_Lean_Meta_whnfD(x_140, x_3, x_4, x_5, x_6, x_125);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
if (lean_obj_tag(x_142) == 7)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_142, 2);
lean_inc(x_147);
lean_dec(x_142);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_146);
x_148 = l_Lean_Meta_getLevel(x_146, x_3, x_4, x_5, x_6, x_143);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_box(0);
x_152 = lean_unbox(x_151);
lean_inc(x_146);
x_153 = l_Lean_Expr_lam___override(x_145, x_146, x_147, x_152);
lean_inc(x_2);
lean_inc(x_153);
x_154 = l_Lean_Expr_app___override(x_153, x_2);
x_155 = l_Lean_Meta_getLevel(x_154, x_3, x_4, x_5, x_6, x_150);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_158 = x_155;
} else {
 lean_dec_ref(x_155);
 x_158 = lean_box(0);
}
x_159 = l_Lean_Expr_appArg_x21(x_138);
lean_dec(x_138);
x_160 = l_Lean_Expr_appArg_x21(x_124);
lean_dec(x_124);
x_161 = lean_mk_string_unchecked("congrFun", 8, 8);
x_162 = l_Lean_Name_mkStr1(x_161);
x_163 = lean_box(0);
if (lean_is_scalar(x_144)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_144;
 lean_ctor_set_tag(x_164, 1);
}
lean_ctor_set(x_164, 0, x_156);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_149);
lean_ctor_set(x_165, 1, x_164);
x_166 = l_Lean_Expr_const___override(x_162, x_165);
x_167 = l_Lean_mkApp6(x_166, x_146, x_153, x_159, x_160, x_1, x_2);
if (lean_is_scalar(x_158)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_158;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_157);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_153);
lean_dec(x_149);
lean_dec(x_146);
lean_dec(x_144);
lean_dec(x_138);
lean_dec(x_124);
lean_dec(x_2);
lean_dec(x_1);
x_169 = lean_ctor_get(x_155, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_155, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_171 = x_155;
} else {
 lean_dec_ref(x_155);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_138);
lean_dec(x_124);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_173 = lean_ctor_get(x_148, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_148, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_175 = x_148;
} else {
 lean_dec_ref(x_148);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_142);
lean_dec(x_138);
lean_dec(x_2);
x_177 = lean_ctor_get(x_141, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_178 = x_141;
} else {
 lean_dec_ref(x_141);
 x_178 = lean_box(0);
}
x_179 = lean_mk_string_unchecked("congrFun", 8, 8);
x_180 = l_Lean_Name_mkStr1(x_179);
x_181 = lean_mk_string_unchecked("equality proof between functions expected", 41, 41);
x_182 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_182, 0, x_181);
x_183 = l_Lean_MessageData_ofFormat(x_182);
x_184 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_124);
if (lean_is_scalar(x_178)) {
 x_185 = lean_alloc_ctor(7, 2, 0);
} else {
 x_185 = x_178;
 lean_ctor_set_tag(x_185, 7);
}
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
x_186 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_180, x_185, x_3, x_4, x_5, x_6, x_177);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_186;
}
}
else
{
lean_dec(x_138);
lean_dec(x_124);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_141;
}
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; uint8_t x_199; lean_object* x_200; 
lean_dec(x_1);
x_187 = lean_ctor_get(x_10, 0);
lean_inc(x_187);
lean_dec(x_10);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_9, 1);
lean_inc(x_189);
lean_dec(x_9);
x_190 = lean_ctor_get(x_187, 0);
lean_inc(x_190);
lean_dec(x_187);
x_191 = lean_ctor_get(x_188, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_188, 1);
lean_inc(x_192);
lean_dec(x_188);
x_193 = lean_alloc_closure((void*)(l_Lean_Meta_mkCongrFun___lam__0___boxed), 8, 2);
lean_closure_set(x_193, 0, x_2);
lean_closure_set(x_193, 1, x_191);
x_194 = lean_mk_string_unchecked("x", 1, 1);
x_195 = l_Lean_Name_mkStr1(x_194);
x_196 = lean_box(0);
x_197 = lean_box(0);
x_198 = lean_unbox(x_196);
x_199 = lean_unbox(x_197);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_200 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___redArg(x_195, x_198, x_190, x_193, x_199, x_3, x_4, x_5, x_6, x_189);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = l_Lean_Meta_mkCongrArg(x_201, x_192, x_3, x_4, x_5, x_6, x_202);
return x_203;
}
else
{
lean_dec(x_192);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_200;
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_204 = !lean_is_exclusive(x_9);
if (x_204 == 0)
{
return x_9;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_9, 0);
x_206 = lean_ctor_get(x_9, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_9);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_1);
x_208 = lean_ctor_get(x_8, 0);
lean_inc(x_208);
lean_dec(x_8);
x_209 = l_Lean_Expr_app___override(x_208, x_2);
x_210 = l_Lean_Meta_mkEqRefl(x_209, x_3, x_4, x_5, x_6, x_7);
return x_210;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrFun___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkCongrFun___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_mk_string_unchecked("Eq", 2, 2);
x_9 = lean_mk_string_unchecked("refl", 4, 4);
lean_inc(x_8);
x_10 = l_Lean_Name_mkStr2(x_8, x_9);
x_11 = l_Lean_Expr_isAppOf(x_1, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isAppOf(x_2, x_10);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_13 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_2, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = l_Lean_Name_mkStr1(x_8);
x_22 = lean_unsigned_to_nat(3u);
x_23 = l_Lean_Expr_isAppOfArity(x_15, x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
lean_dec(x_19);
lean_free_object(x_13);
lean_dec(x_2);
x_24 = lean_mk_string_unchecked("congr", 5, 5);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_MessageData_ofFormat(x_27);
x_29 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_15);
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_29);
lean_ctor_set(x_17, 0, x_28);
x_30 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_25, x_17, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = l_Lean_Expr_isAppOfArity(x_19, x_21, x_22);
lean_dec(x_21);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_1);
x_32 = lean_mk_string_unchecked("congr", 5, 5);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Lean_MessageData_ofFormat(x_35);
x_37 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_19);
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_37);
lean_ctor_set(x_17, 0, x_36);
x_38 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_33, x_17, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = l_Lean_Expr_appFn_x21(x_15);
x_40 = l_Lean_Expr_appFn_x21(x_39);
x_41 = l_Lean_Expr_appArg_x21(x_40);
lean_dec(x_40);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_42 = l_Lean_Meta_whnfD(x_41, x_3, x_4, x_5, x_6, x_20);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
if (lean_obj_tag(x_43) == 7)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_43, 2);
lean_inc(x_55);
lean_dec(x_43);
x_56 = l_Lean_Expr_hasLooseBVars(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_45);
x_57 = l_Lean_Expr_appFn_x21(x_19);
x_58 = l_Lean_Expr_appFn_x21(x_57);
x_59 = l_Lean_Expr_appArg_x21(x_58);
lean_dec(x_58);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_59);
x_60 = l_Lean_Meta_getLevel(x_59, x_3, x_4, x_5, x_6, x_44);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_55);
x_63 = l_Lean_Meta_getLevel(x_55, x_3, x_4, x_5, x_6, x_62);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = l_Lean_Expr_appArg_x21(x_39);
lean_dec(x_39);
x_67 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
x_68 = l_Lean_Expr_appArg_x21(x_57);
lean_dec(x_57);
x_69 = l_Lean_Expr_appArg_x21(x_19);
lean_dec(x_19);
x_70 = lean_mk_string_unchecked("congr", 5, 5);
x_71 = l_Lean_Name_mkStr1(x_70);
x_72 = lean_box(0);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_72);
lean_ctor_set(x_17, 0, x_65);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_17);
lean_ctor_set(x_13, 0, x_61);
x_73 = l_Lean_Expr_const___override(x_71, x_13);
x_74 = l_Lean_mkApp8(x_73, x_59, x_55, x_66, x_67, x_68, x_69, x_1, x_2);
lean_ctor_set(x_63, 0, x_74);
return x_63;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_75 = lean_ctor_get(x_63, 0);
x_76 = lean_ctor_get(x_63, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_63);
x_77 = l_Lean_Expr_appArg_x21(x_39);
lean_dec(x_39);
x_78 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
x_79 = l_Lean_Expr_appArg_x21(x_57);
lean_dec(x_57);
x_80 = l_Lean_Expr_appArg_x21(x_19);
lean_dec(x_19);
x_81 = lean_mk_string_unchecked("congr", 5, 5);
x_82 = l_Lean_Name_mkStr1(x_81);
x_83 = lean_box(0);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_83);
lean_ctor_set(x_17, 0, x_75);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_17);
lean_ctor_set(x_13, 0, x_61);
x_84 = l_Lean_Expr_const___override(x_82, x_13);
x_85 = l_Lean_mkApp8(x_84, x_59, x_55, x_77, x_78, x_79, x_80, x_1, x_2);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_76);
return x_86;
}
}
else
{
uint8_t x_87; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_39);
lean_free_object(x_17);
lean_dec(x_19);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_63);
if (x_87 == 0)
{
return x_63;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_63, 0);
x_89 = lean_ctor_get(x_63, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_63);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_39);
lean_free_object(x_17);
lean_dec(x_19);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_60);
if (x_91 == 0)
{
return x_60;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_60, 0);
x_93 = lean_ctor_get(x_60, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_60);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_dec(x_55);
lean_dec(x_39);
lean_free_object(x_17);
lean_dec(x_19);
lean_free_object(x_13);
lean_dec(x_2);
goto block_54;
}
}
else
{
lean_dec(x_43);
lean_dec(x_39);
lean_free_object(x_17);
lean_dec(x_19);
lean_free_object(x_13);
lean_dec(x_2);
goto block_54;
}
block_54:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_mk_string_unchecked("congr", 5, 5);
x_47 = l_Lean_Name_mkStr1(x_46);
x_48 = lean_mk_string_unchecked("non-dependent function expected", 31, 31);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_MessageData_ofFormat(x_49);
x_51 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_15);
if (lean_is_scalar(x_45)) {
 x_52 = lean_alloc_ctor(7, 2, 0);
} else {
 x_52 = x_45;
 lean_ctor_set_tag(x_52, 7);
}
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_47, x_52, x_3, x_4, x_5, x_6, x_44);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_53;
}
}
else
{
lean_dec(x_39);
lean_free_object(x_17);
lean_dec(x_19);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_42;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_95 = lean_ctor_get(x_17, 0);
x_96 = lean_ctor_get(x_17, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_17);
x_97 = l_Lean_Name_mkStr1(x_8);
x_98 = lean_unsigned_to_nat(3u);
x_99 = l_Lean_Expr_isAppOfArity(x_15, x_97, x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_97);
lean_dec(x_95);
lean_free_object(x_13);
lean_dec(x_2);
x_100 = lean_mk_string_unchecked("congr", 5, 5);
x_101 = l_Lean_Name_mkStr1(x_100);
x_102 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_103 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = l_Lean_MessageData_ofFormat(x_103);
x_105 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_15);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_101, x_106, x_3, x_4, x_5, x_6, x_96);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_107;
}
else
{
uint8_t x_108; 
x_108 = l_Lean_Expr_isAppOfArity(x_95, x_97, x_98);
lean_dec(x_97);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_1);
x_109 = lean_mk_string_unchecked("congr", 5, 5);
x_110 = l_Lean_Name_mkStr1(x_109);
x_111 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l_Lean_MessageData_ofFormat(x_112);
x_114 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_95);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_110, x_115, x_3, x_4, x_5, x_6, x_96);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = l_Lean_Expr_appFn_x21(x_15);
x_118 = l_Lean_Expr_appFn_x21(x_117);
x_119 = l_Lean_Expr_appArg_x21(x_118);
lean_dec(x_118);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_120 = l_Lean_Meta_whnfD(x_119, x_3, x_4, x_5, x_6, x_96);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_123 = x_120;
} else {
 lean_dec_ref(x_120);
 x_123 = lean_box(0);
}
if (lean_obj_tag(x_121) == 7)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_121, 2);
lean_inc(x_133);
lean_dec(x_121);
x_134 = l_Lean_Expr_hasLooseBVars(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_123);
x_135 = l_Lean_Expr_appFn_x21(x_95);
x_136 = l_Lean_Expr_appFn_x21(x_135);
x_137 = l_Lean_Expr_appArg_x21(x_136);
lean_dec(x_136);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_137);
x_138 = l_Lean_Meta_getLevel(x_137, x_3, x_4, x_5, x_6, x_122);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
lean_inc(x_133);
x_141 = l_Lean_Meta_getLevel(x_133, x_3, x_4, x_5, x_6, x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
x_145 = l_Lean_Expr_appArg_x21(x_117);
lean_dec(x_117);
x_146 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
x_147 = l_Lean_Expr_appArg_x21(x_135);
lean_dec(x_135);
x_148 = l_Lean_Expr_appArg_x21(x_95);
lean_dec(x_95);
x_149 = lean_mk_string_unchecked("congr", 5, 5);
x_150 = l_Lean_Name_mkStr1(x_149);
x_151 = lean_box(0);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_142);
lean_ctor_set(x_152, 1, x_151);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_152);
lean_ctor_set(x_13, 0, x_139);
x_153 = l_Lean_Expr_const___override(x_150, x_13);
x_154 = l_Lean_mkApp8(x_153, x_137, x_133, x_145, x_146, x_147, x_148, x_1, x_2);
if (lean_is_scalar(x_144)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_144;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_143);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_117);
lean_dec(x_95);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_156 = lean_ctor_get(x_141, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_141, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_158 = x_141;
} else {
 lean_dec_ref(x_141);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_137);
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_117);
lean_dec(x_95);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_160 = lean_ctor_get(x_138, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_138, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_162 = x_138;
} else {
 lean_dec_ref(x_138);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
else
{
lean_dec(x_133);
lean_dec(x_117);
lean_dec(x_95);
lean_free_object(x_13);
lean_dec(x_2);
goto block_132;
}
}
else
{
lean_dec(x_121);
lean_dec(x_117);
lean_dec(x_95);
lean_free_object(x_13);
lean_dec(x_2);
goto block_132;
}
block_132:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_124 = lean_mk_string_unchecked("congr", 5, 5);
x_125 = l_Lean_Name_mkStr1(x_124);
x_126 = lean_mk_string_unchecked("non-dependent function expected", 31, 31);
x_127 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = l_Lean_MessageData_ofFormat(x_127);
x_129 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_15);
if (lean_is_scalar(x_123)) {
 x_130 = lean_alloc_ctor(7, 2, 0);
} else {
 x_130 = x_123;
 lean_ctor_set_tag(x_130, 7);
}
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_125, x_130, x_3, x_4, x_5, x_6, x_122);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_131;
}
}
else
{
lean_dec(x_117);
lean_dec(x_95);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_120;
}
}
}
}
}
else
{
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_13, 0);
x_165 = lean_ctor_get(x_13, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_166 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_2, x_3, x_4, x_5, x_6, x_165);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_169 = x_166;
} else {
 lean_dec_ref(x_166);
 x_169 = lean_box(0);
}
x_170 = l_Lean_Name_mkStr1(x_8);
x_171 = lean_unsigned_to_nat(3u);
x_172 = l_Lean_Expr_isAppOfArity(x_164, x_170, x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_170);
lean_dec(x_167);
lean_dec(x_2);
x_173 = lean_mk_string_unchecked("congr", 5, 5);
x_174 = l_Lean_Name_mkStr1(x_173);
x_175 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_176 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_176, 0, x_175);
x_177 = l_Lean_MessageData_ofFormat(x_176);
x_178 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_164);
if (lean_is_scalar(x_169)) {
 x_179 = lean_alloc_ctor(7, 2, 0);
} else {
 x_179 = x_169;
 lean_ctor_set_tag(x_179, 7);
}
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_174, x_179, x_3, x_4, x_5, x_6, x_168);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_180;
}
else
{
uint8_t x_181; 
x_181 = l_Lean_Expr_isAppOfArity(x_167, x_170, x_171);
lean_dec(x_170);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_164);
lean_dec(x_1);
x_182 = lean_mk_string_unchecked("congr", 5, 5);
x_183 = l_Lean_Name_mkStr1(x_182);
x_184 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_185 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_185, 0, x_184);
x_186 = l_Lean_MessageData_ofFormat(x_185);
x_187 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_167);
if (lean_is_scalar(x_169)) {
 x_188 = lean_alloc_ctor(7, 2, 0);
} else {
 x_188 = x_169;
 lean_ctor_set_tag(x_188, 7);
}
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
x_189 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_183, x_188, x_3, x_4, x_5, x_6, x_168);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_190 = l_Lean_Expr_appFn_x21(x_164);
x_191 = l_Lean_Expr_appFn_x21(x_190);
x_192 = l_Lean_Expr_appArg_x21(x_191);
lean_dec(x_191);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_193 = l_Lean_Meta_whnfD(x_192, x_3, x_4, x_5, x_6, x_168);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_196 = x_193;
} else {
 lean_dec_ref(x_193);
 x_196 = lean_box(0);
}
if (lean_obj_tag(x_194) == 7)
{
lean_object* x_206; uint8_t x_207; 
x_206 = lean_ctor_get(x_194, 2);
lean_inc(x_206);
lean_dec(x_194);
x_207 = l_Lean_Expr_hasLooseBVars(x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_196);
x_208 = l_Lean_Expr_appFn_x21(x_167);
x_209 = l_Lean_Expr_appFn_x21(x_208);
x_210 = l_Lean_Expr_appArg_x21(x_209);
lean_dec(x_209);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_210);
x_211 = l_Lean_Meta_getLevel(x_210, x_3, x_4, x_5, x_6, x_195);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
lean_inc(x_206);
x_214 = l_Lean_Meta_getLevel(x_206, x_3, x_4, x_5, x_6, x_213);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_217 = x_214;
} else {
 lean_dec_ref(x_214);
 x_217 = lean_box(0);
}
x_218 = l_Lean_Expr_appArg_x21(x_190);
lean_dec(x_190);
x_219 = l_Lean_Expr_appArg_x21(x_164);
lean_dec(x_164);
x_220 = l_Lean_Expr_appArg_x21(x_208);
lean_dec(x_208);
x_221 = l_Lean_Expr_appArg_x21(x_167);
lean_dec(x_167);
x_222 = lean_mk_string_unchecked("congr", 5, 5);
x_223 = l_Lean_Name_mkStr1(x_222);
x_224 = lean_box(0);
if (lean_is_scalar(x_169)) {
 x_225 = lean_alloc_ctor(1, 2, 0);
} else {
 x_225 = x_169;
 lean_ctor_set_tag(x_225, 1);
}
lean_ctor_set(x_225, 0, x_215);
lean_ctor_set(x_225, 1, x_224);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_212);
lean_ctor_set(x_226, 1, x_225);
x_227 = l_Lean_Expr_const___override(x_223, x_226);
x_228 = l_Lean_mkApp8(x_227, x_210, x_206, x_218, x_219, x_220, x_221, x_1, x_2);
if (lean_is_scalar(x_217)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_217;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_216);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_212);
lean_dec(x_210);
lean_dec(x_208);
lean_dec(x_206);
lean_dec(x_190);
lean_dec(x_169);
lean_dec(x_167);
lean_dec(x_164);
lean_dec(x_2);
lean_dec(x_1);
x_230 = lean_ctor_get(x_214, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_214, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_232 = x_214;
} else {
 lean_dec_ref(x_214);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_210);
lean_dec(x_208);
lean_dec(x_206);
lean_dec(x_190);
lean_dec(x_169);
lean_dec(x_167);
lean_dec(x_164);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_234 = lean_ctor_get(x_211, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_211, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_236 = x_211;
} else {
 lean_dec_ref(x_211);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
}
else
{
lean_dec(x_206);
lean_dec(x_190);
lean_dec(x_169);
lean_dec(x_167);
lean_dec(x_2);
goto block_205;
}
}
else
{
lean_dec(x_194);
lean_dec(x_190);
lean_dec(x_169);
lean_dec(x_167);
lean_dec(x_2);
goto block_205;
}
block_205:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_197 = lean_mk_string_unchecked("congr", 5, 5);
x_198 = l_Lean_Name_mkStr1(x_197);
x_199 = lean_mk_string_unchecked("non-dependent function expected", 31, 31);
x_200 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_200, 0, x_199);
x_201 = l_Lean_MessageData_ofFormat(x_200);
x_202 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_164);
if (lean_is_scalar(x_196)) {
 x_203 = lean_alloc_ctor(7, 2, 0);
} else {
 x_203 = x_196;
 lean_ctor_set_tag(x_203, 7);
}
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_198, x_203, x_3, x_4, x_5, x_6, x_195);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_204;
}
}
else
{
lean_dec(x_190);
lean_dec(x_169);
lean_dec(x_167);
lean_dec(x_164);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_193;
}
}
}
}
else
{
lean_dec(x_164);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_166;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_8);
x_238 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_239 = l_Lean_Meta_mkCongrFun(x_1, x_238, x_3, x_4, x_5, x_6, x_7);
return x_239;
}
}
else
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_10);
lean_dec(x_8);
x_240 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
x_241 = l_Lean_Meta_mkCongrArg(x_240, x_2, x_3, x_4, x_5, x_6, x_7);
return x_241;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_7);
x_8 = l_Lean_MetavarContext_getDecl(x_7, x_1);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = lean_box(x_11);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_15);
x_16 = l_Lean_MetavarContext_getDecl(x_15, x_1);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_nat_dec_eq(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_11 = l_instMonadEIO(lean_box(0));
x_12 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_24, 0, lean_box(0));
lean_closure_set(x_24, 1, lean_box(0));
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_25);
lean_inc(x_26);
lean_inc(x_23);
lean_inc(x_20);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_9);
lean_ctor_set(x_27, 2, x_20);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
x_29 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_31);
x_32 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_32, 0, x_31);
x_33 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_33, 0, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_35, 0, x_20);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_37, 0, x_23);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_39, 0, x_26);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_7);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 3, x_38);
lean_ctor_set(x_41, 4, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_8);
x_43 = l_instInhabitedBool;
x_44 = lean_box(x_43);
x_45 = l_instInhabitedOfMonad___redArg(x_42, x_44);
x_46 = lean_panic_fn(x_45, x_1);
x_47 = lean_apply_5(x_46, x_2, x_3, x_4, x_5, x_6);
return x_47;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_3, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
x_13 = l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___redArg(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_free_object(x_7);
x_14 = lean_mk_string_unchecked("Lean.MetavarContext", 19, 19);
x_15 = lean_mk_string_unchecked("Lean.isLevelMVarAssignable", 26, 26);
x_16 = lean_unsigned_to_nat(425u);
x_17 = lean_unsigned_to_nat(14u);
x_18 = lean_mk_string_unchecked("unknown universe metavariable", 29, 29);
x_19 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_14, x_15, x_16, x_17, x_18);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
x_20 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1_spec__1_spec__1(x_19, x_2, x_3, x_4, x_5, x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_nat_dec_le(x_22, x_21);
lean_dec(x_21);
lean_dec(x_22);
x_24 = lean_box(x_23);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
x_29 = l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___redArg(x_28, x_1);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_27);
x_30 = lean_mk_string_unchecked("Lean.MetavarContext", 19, 19);
x_31 = lean_mk_string_unchecked("Lean.isLevelMVarAssignable", 26, 26);
x_32 = lean_unsigned_to_nat(425u);
x_33 = lean_unsigned_to_nat(14u);
x_34 = lean_mk_string_unchecked("unknown universe metavariable", 29, 29);
x_35 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_30, x_31, x_32, x_33, x_34);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
x_36 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1_spec__1_spec__1(x_35, x_2, x_3, x_4, x_5, x_26);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_dec(x_27);
x_39 = lean_nat_dec_le(x_38, x_37);
lean_dec(x_37);
lean_dec(x_38);
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_26);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_16; 
x_16 = l_Lean_Level_hasMVar(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(x_16);
lean_inc(x_7);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
x_8 = x_18;
x_9 = x_16;
x_10 = x_7;
goto block_15;
}
else
{
lean_object* x_19; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = lean_unbox(x_20);
lean_dec(x_20);
x_8 = x_19;
x_9 = x_22;
x_10 = x_21;
goto block_15;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
}
block_15:
{
if (x_9 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
x_11 = l_Lean_Level_hasMVar(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1(x_2, x_3, x_4, x_5, x_6, x_10);
return x_14;
}
}
else
{
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_Lean_Level_hasMVar(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1___lam__0(x_12, x_13, x_2, x_3, x_4, x_5, x_6);
return x_14;
}
case 3:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1___lam__0(x_15, x_16, x_2, x_3, x_4, x_5, x_6);
return x_17;
}
case 5:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1_spec__1(x_18, x_2, x_3, x_4, x_5, x_6);
return x_19;
}
default: 
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1(x_9, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_1 = x_10;
x_6 = x_14;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; uint8_t x_18; 
x_18 = l_Lean_Expr_hasMVar(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(x_18);
lean_inc(x_9);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_9);
x_10 = x_20;
x_11 = x_18;
x_12 = x_9;
goto block_17;
}
else
{
lean_object* x_21; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = lean_unbox(x_22);
lean_dec(x_22);
x_10 = x_21;
x_11 = x_24;
x_12 = x_23;
goto block_17;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_21;
}
}
block_17:
{
if (x_11 == 0)
{
uint8_t x_13; 
lean_dec(x_10);
x_13 = l_Lean_Expr_hasMVar(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(x_3, x_5, x_6, x_7, x_8, x_12);
return x_16;
}
}
else
{
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(x_7, x_3, x_6);
lean_dec(x_3);
return x_8;
}
case 3:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
case 4:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = l_List_anyM___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__4(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
case 5:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_23; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_23 = l_Lean_Expr_hasMVar(x_13);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(x_23);
lean_inc(x_6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_6);
x_15 = x_25;
x_16 = x_23;
x_17 = x_6;
goto block_22;
}
else
{
lean_object* x_26; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_26 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
x_29 = lean_unbox(x_27);
lean_dec(x_27);
x_15 = x_26;
x_16 = x_29;
x_17 = x_28;
goto block_22;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_26;
}
}
block_22:
{
if (x_16 == 0)
{
uint8_t x_18; 
lean_dec(x_15);
x_18 = l_Lean_Expr_hasMVar(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
else
{
x_1 = x_14;
x_6 = x_17;
goto _start;
}
}
else
{
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
}
case 6:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_1, 0);
x_31 = lean_ctor_get(x_1, 1);
x_32 = lean_ctor_get(x_1, 2);
x_33 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_34 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___lam__0(x_30, x_31, x_32, x_33, x_2, x_3, x_4, x_5, x_6);
return x_34;
}
case 7:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_39 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___lam__0(x_35, x_36, x_37, x_38, x_2, x_3, x_4, x_5, x_6);
return x_39;
}
case 8:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_51; uint8_t x_52; lean_object* x_53; uint8_t x_62; 
x_40 = lean_ctor_get(x_1, 1);
x_41 = lean_ctor_get(x_1, 2);
x_42 = lean_ctor_get(x_1, 3);
x_62 = l_Lean_Expr_hasMVar(x_40);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_box(x_62);
lean_inc(x_6);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_6);
x_51 = x_64;
x_52 = x_62;
x_53 = x_6;
goto block_61;
}
else
{
lean_object* x_65; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_65 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(x_40, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
x_68 = lean_unbox(x_66);
lean_dec(x_66);
x_51 = x_65;
x_52 = x_68;
x_53 = x_67;
goto block_61;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_65;
}
}
block_50:
{
if (x_44 == 0)
{
uint8_t x_46; 
lean_dec(x_43);
x_46 = l_Lean_Expr_hasMVar(x_42);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
else
{
x_1 = x_42;
x_6 = x_45;
goto _start;
}
}
else
{
lean_dec(x_45);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_43;
}
}
block_61:
{
if (x_52 == 0)
{
uint8_t x_54; 
lean_dec(x_51);
x_54 = l_Lean_Expr_hasMVar(x_41);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_box(x_54);
lean_inc(x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
x_43 = x_56;
x_44 = x_54;
x_45 = x_53;
goto block_50;
}
else
{
lean_object* x_57; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_57 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(x_41, x_2, x_3, x_4, x_5, x_53);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
x_60 = lean_unbox(x_58);
lean_dec(x_58);
x_43 = x_57;
x_44 = x_60;
x_45 = x_59;
goto block_50;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_57;
}
}
}
else
{
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_51;
}
}
}
case 10:
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_1, 1);
x_70 = l_Lean_Expr_hasMVar(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_box(x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_6);
return x_72;
}
else
{
x_1 = x_69;
goto _start;
}
}
case 11:
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_1, 2);
x_75 = l_Lean_Expr_hasMVar(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = lean_box(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_6);
return x_77;
}
else
{
x_1 = x_74;
goto _start;
}
}
default: 
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_6);
return x_80;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = lean_array_uget(x_1, x_2);
lean_inc(x_11);
x_12 = l_Lean_MVarId_getDecl(x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 2);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Meta_synthInstance(x_15, x_16, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_11, x_18, x_6, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_add(x_2, x_24);
x_2 = x_25;
x_4 = x_21;
x_9 = x_22;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
return x_12;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_12, 0);
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_12);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_4);
lean_ctor_set(x_35, 1, x_9);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_array_get_size(x_4);
x_63 = lean_nat_dec_lt(x_61, x_62);
if (x_63 == 0)
{
lean_dec(x_62);
x_10 = x_9;
goto block_60;
}
else
{
uint8_t x_64; 
x_64 = lean_nat_dec_le(x_62, x_62);
if (x_64 == 0)
{
lean_dec(x_62);
x_10 = x_9;
goto block_60;
}
else
{
lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; 
x_65 = lean_box(0);
x_66 = lean_usize_of_nat(x_61);
x_67 = lean_usize_of_nat(x_62);
lean_dec(x_62);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_68 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__6(x_4, x_66, x_67, x_65, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_10 = x_69;
goto block_60;
}
else
{
uint8_t x_70; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_68);
if (x_70 == 0)
{
return x_68;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_68, 0);
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_68);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
block_60:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_mkAppN(x_2, x_3);
x_12 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_11, x_6, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(x_14, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_free_object(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_mk_string_unchecked("result contains metavariables", 29, 29);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_MessageData_ofFormat(x_25);
x_27 = l_Lean_indentExpr(x_14);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_27);
lean_ctor_set(x_12, 0, x_26);
x_28 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_1, x_12, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_free_object(x_12);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_12, 0);
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_39 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(x_37, x_5, x_6, x_7, x_8, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_43 = x_39;
} else {
 lean_dec_ref(x_39);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_mk_string_unchecked("result contains metavariables", 29, 29);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Lean_MessageData_ofFormat(x_47);
x_49 = l_Lean_indentExpr(x_37);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_1, x_50, x_5, x_6, x_7, x_8, x_45);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_56 = lean_ctor_get(x_39, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_58 = x_39;
} else {
 lean_dec_ref(x_39);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_anyM___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___lam__0(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__6(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_2);
x_14 = lean_nat_dec_le(x_13, x_4);
lean_dec(x_13);
if (x_14 == 0)
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_dec(x_3);
x_19 = lean_array_get_size(x_6);
x_20 = lean_expr_instantiate_rev_range(x_16, x_5, x_19, x_6);
lean_dec(x_19);
lean_dec(x_16);
x_21 = lean_box(x_18);
switch (lean_obj_tag(x_21)) {
case 0:
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_15);
x_22 = lean_array_fget(x_2, x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_22);
x_23 = lean_infer_type(x_22, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_79 = lean_box(1);
x_80 = lean_ctor_get(x_8, 0);
lean_inc(x_80);
x_81 = lean_ctor_get_uint8(x_80, 9);
lean_dec(x_80);
x_82 = lean_unbox(x_79);
x_83 = l_Lean_Meta_TransparencyMode_lt(x_81, x_82);
if (x_83 == 0)
{
x_26 = x_81;
goto block_78;
}
else
{
uint8_t x_84; 
x_84 = lean_unbox(x_79);
x_26 = x_84;
goto block_78;
}
block_78:
{
lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; uint64_t x_46; lean_object* x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_27 = lean_ctor_get(x_8, 0);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_27, 0);
x_29 = lean_ctor_get_uint8(x_27, 1);
x_30 = lean_ctor_get_uint8(x_27, 2);
x_31 = lean_ctor_get_uint8(x_27, 3);
x_32 = lean_ctor_get_uint8(x_27, 4);
x_33 = lean_ctor_get_uint8(x_27, 5);
x_34 = lean_ctor_get_uint8(x_27, 6);
x_35 = lean_ctor_get_uint8(x_27, 7);
x_36 = lean_ctor_get_uint8(x_27, 8);
x_37 = lean_ctor_get_uint8(x_27, 10);
x_38 = lean_ctor_get_uint8(x_27, 11);
x_39 = lean_ctor_get_uint8(x_27, 12);
x_40 = lean_ctor_get_uint8(x_27, 13);
x_41 = lean_ctor_get_uint8(x_27, 14);
x_42 = lean_ctor_get_uint8(x_27, 15);
x_43 = lean_ctor_get_uint8(x_27, 16);
x_44 = lean_ctor_get_uint8(x_27, 17);
lean_dec(x_27);
x_45 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_45, 0, x_28);
lean_ctor_set_uint8(x_45, 1, x_29);
lean_ctor_set_uint8(x_45, 2, x_30);
lean_ctor_set_uint8(x_45, 3, x_31);
lean_ctor_set_uint8(x_45, 4, x_32);
lean_ctor_set_uint8(x_45, 5, x_33);
lean_ctor_set_uint8(x_45, 6, x_34);
lean_ctor_set_uint8(x_45, 7, x_35);
lean_ctor_set_uint8(x_45, 8, x_36);
lean_ctor_set_uint8(x_45, 9, x_26);
lean_ctor_set_uint8(x_45, 10, x_37);
lean_ctor_set_uint8(x_45, 11, x_38);
lean_ctor_set_uint8(x_45, 12, x_39);
lean_ctor_set_uint8(x_45, 13, x_40);
lean_ctor_set_uint8(x_45, 14, x_41);
lean_ctor_set_uint8(x_45, 15, x_42);
lean_ctor_set_uint8(x_45, 16, x_43);
lean_ctor_set_uint8(x_45, 17, x_44);
x_46 = lean_ctor_get_uint64(x_8, sizeof(void*)*7);
x_47 = lean_unsigned_to_nat(2u);
x_48 = lean_uint64_of_nat(x_47);
x_49 = lean_uint64_shift_right(x_46, x_48);
x_50 = lean_uint64_shift_left(x_49, x_48);
x_51 = l_Lean_Meta_TransparencyMode_toUInt64(x_26);
x_52 = lean_uint64_lor(x_50, x_51);
x_53 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 8);
x_54 = lean_ctor_get(x_8, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_8, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_8, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_8, 4);
lean_inc(x_57);
x_58 = lean_ctor_get(x_8, 5);
lean_inc(x_58);
x_59 = lean_ctor_get(x_8, 6);
lean_inc(x_59);
x_60 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 9);
x_61 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 10);
x_62 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_62, 0, x_45);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_55);
lean_ctor_set(x_62, 3, x_56);
lean_ctor_set(x_62, 4, x_57);
lean_ctor_set(x_62, 5, x_58);
lean_ctor_set(x_62, 6, x_59);
lean_ctor_set_uint64(x_62, sizeof(void*)*7, x_52);
lean_ctor_set_uint8(x_62, sizeof(void*)*7 + 8, x_53);
lean_ctor_set_uint8(x_62, sizeof(void*)*7 + 9, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*7 + 10, x_61);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_63 = l_Lean_Meta_isExprDefEq(x_20, x_24, x_62, x_9, x_10, x_11, x_25);
lean_dec(x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = l_Lean_mkAppN(x_1, x_6);
lean_dec(x_6);
x_68 = l_Lean_Meta_throwAppTypeMismatch___redArg(x_67, x_22, x_8, x_9, x_10, x_11, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
lean_dec(x_63);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_4, x_70);
lean_dec(x_4);
x_72 = lean_array_push(x_6, x_22);
x_3 = x_17;
x_4 = x_71;
x_6 = x_72;
x_12 = x_69;
goto _start;
}
}
else
{
uint8_t x_74; 
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_63);
if (x_74 == 0)
{
return x_63;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_63, 0);
x_76 = lean_ctor_get(x_63, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_63);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
else
{
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_23;
}
}
case 3:
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_20);
x_86 = lean_box(1);
x_87 = lean_unbox(x_86);
lean_inc(x_8);
x_88 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_85, x_87, x_15, x_8, x_9, x_10, x_11, x_12);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
lean_inc(x_89);
x_91 = lean_array_push(x_6, x_89);
x_92 = l_Lean_Expr_mvarId_x21(x_89);
lean_dec(x_89);
x_93 = lean_array_push(x_7, x_92);
x_3 = x_17;
x_6 = x_91;
x_7 = x_93;
x_12 = x_90;
goto _start;
}
default: 
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_21);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_20);
x_96 = lean_box(0);
x_97 = lean_unbox(x_96);
lean_inc(x_8);
x_98 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_95, x_97, x_15, x_8, x_9, x_10, x_11, x_12);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_array_push(x_6, x_99);
x_3 = x_17;
x_6 = x_101;
x_12 = x_100;
goto _start;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_array_get_size(x_6);
x_104 = lean_expr_instantiate_rev_range(x_3, x_5, x_103, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_105 = l_Lean_Meta_whnfD(x_104, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = lean_ctor_get(x_105, 1);
x_109 = l_Lean_Expr_isForall(x_107);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_107);
lean_dec(x_103);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_110 = lean_mk_string_unchecked("mkAppM", 6, 6);
x_111 = l_Lean_Name_mkStr1(x_110);
x_112 = lean_mk_string_unchecked("too many explicit arguments provided to", 39, 39);
x_113 = l_Lean_stringToMessageData(x_112);
lean_dec(x_112);
x_114 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_105, 7);
lean_ctor_set(x_105, 1, x_114);
lean_ctor_set(x_105, 0, x_113);
x_115 = lean_mk_string_unchecked("\narguments", 10, 10);
x_116 = l_Lean_stringToMessageData(x_115);
lean_dec(x_115);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_105);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_unsigned_to_nat(0u);
x_119 = lean_mk_string_unchecked("#[", 2, 2);
x_120 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = l_Lean_MessageData_ofFormat(x_120);
x_122 = l_Lean_MessageData_arrayExpr_toMessageData(x_2, x_118, x_121);
x_123 = l_Lean_indentD(x_122);
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_117);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_mk_string_unchecked("", 0, 0);
x_126 = l_Lean_stringToMessageData(x_125);
lean_dec(x_125);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_126);
x_128 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_111, x_127, x_8, x_9, x_10, x_11, x_108);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_128;
}
else
{
lean_free_object(x_105);
x_3 = x_107;
x_5 = x_103;
x_12 = x_108;
goto _start;
}
}
else
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = lean_ctor_get(x_105, 0);
x_131 = lean_ctor_get(x_105, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_105);
x_132 = l_Lean_Expr_isForall(x_130);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_130);
lean_dec(x_103);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_133 = lean_mk_string_unchecked("mkAppM", 6, 6);
x_134 = l_Lean_Name_mkStr1(x_133);
x_135 = lean_mk_string_unchecked("too many explicit arguments provided to", 39, 39);
x_136 = l_Lean_stringToMessageData(x_135);
lean_dec(x_135);
x_137 = l_Lean_indentExpr(x_1);
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_mk_string_unchecked("\narguments", 10, 10);
x_140 = l_Lean_stringToMessageData(x_139);
lean_dec(x_139);
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_unsigned_to_nat(0u);
x_143 = lean_mk_string_unchecked("#[", 2, 2);
x_144 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_145 = l_Lean_MessageData_ofFormat(x_144);
x_146 = l_Lean_MessageData_arrayExpr_toMessageData(x_2, x_142, x_145);
x_147 = l_Lean_indentD(x_146);
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_141);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_mk_string_unchecked("", 0, 0);
x_150 = l_Lean_stringToMessageData(x_149);
lean_dec(x_149);
x_151 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_150);
x_152 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_134, x_151, x_8, x_9, x_10, x_11, x_131);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_152;
}
else
{
x_3 = x_130;
x_5 = x_103;
x_12 = x_131;
goto _start;
}
}
}
else
{
lean_dec(x_103);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_105;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_154 = lean_mk_string_unchecked("mkAppM", 6, 6);
x_155 = l_Lean_Name_mkStr1(x_154);
x_156 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_155, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
return x_156;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
lean_inc(x_10);
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(x_1, x_3, x_2, x_9, x_9, x_10, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_List_reverse___redArg(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
x_13 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_11;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_15;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_7);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_2);
x_1 = x_17;
x_2 = x_21;
x_7 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = l_List_mapM_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(x_10, x_11, x_2, x_3, x_4, x_5, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_16 = l_Lean_Core_instantiateTypeLevelParams___redArg(x_8, x_14, x_5, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l_Lean_Expr_const___override(x_1, x_14);
lean_ctor_set(x_12, 1, x_18);
lean_ctor_set(x_12, 0, x_19);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = l_Lean_Expr_const___override(x_1, x_14);
lean_ctor_set(x_12, 1, x_20);
lean_ctor_set(x_12, 0, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
lean_inc(x_24);
x_26 = l_Lean_Core_instantiateTypeLevelParams___redArg(x_8, x_24, x_5, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = l_Lean_Expr_const___override(x_1, x_24);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_29;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_7);
if (x_33 == 0)
{
return x_7;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_7, 0);
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_7);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_instMonadLiftT(lean_box(0));
x_4 = lean_apply_2(x_3, lean_box(0), x_2);
x_5 = l_instMonadLiftBaseIOEIO(lean_box(0));
x_6 = lean_apply_2(x_5, lean_box(0), x_4);
x_7 = l_Lean_Core_instMonadLiftIOCoreM;
x_8 = lean_apply_2(x_7, lean_box(0), x_6);
x_9 = l_StateRefT_x27_instMonadLift(lean_box(0), lean_box(0), lean_box(0));
x_10 = lean_apply_2(x_9, lean_box(0), x_8);
x_11 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_mk_string_unchecked("", 0, 0);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_29; 
x_29 = lean_mk_string_unchecked("❌️", 6, 2);
x_13 = x_29;
goto block_28;
}
else
{
lean_object* x_30; 
x_30 = lean_mk_string_unchecked("✅️", 6, 2);
x_13 = x_30;
goto block_28;
}
block_28:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = l_Lean_stringToMessageData(x_13);
lean_inc(x_12);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_mk_string_unchecked(" f: ", 4, 4);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_apply_1(x_1, x_2);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked(", xs: ", 6, 6);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_apply_1(x_3, x_4);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_12);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_10);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_45; lean_object* x_46; lean_object* x_50; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_50 = lean_apply_5(x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_mk_string_unchecked("result", 6, 6);
lean_inc(x_2);
lean_inc(x_1);
x_54 = l_Lean_Name_mkStr3(x_1, x_2, x_53);
lean_inc(x_54);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_55 = l_Lean_isTracingEnabledFor___redArg(x_3, x_4, x_5, x_54);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_56 = lean_apply_5(x_55, x_9, x_10, x_11, x_12, x_52);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
uint8_t x_59; 
lean_dec(x_54);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_56, 0);
lean_dec(x_60);
lean_ctor_set(x_56, 0, x_51);
return x_56;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_dec(x_56);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_51);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_dec(x_56);
lean_inc(x_51);
x_64 = l_Lean_MessageData_ofExpr(x_51);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
x_65 = l_Lean_addTrace___redArg(x_3, x_4, x_6, x_7, x_54, x_64);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_66 = lean_apply_5(x_65, x_9, x_10, x_11, x_12, x_63);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
lean_ctor_set(x_66, 0, x_51);
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_51);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_51);
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_dec(x_66);
x_45 = x_71;
x_46 = x_72;
goto block_49;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_54);
lean_dec(x_51);
x_73 = lean_ctor_get(x_56, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_56, 1);
lean_inc(x_74);
lean_dec(x_56);
x_45 = x_73;
x_46 = x_74;
goto block_49;
}
}
else
{
if (lean_obj_tag(x_50) == 0)
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_50;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_50, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_50, 1);
lean_inc(x_76);
lean_dec(x_50);
x_45 = x_75;
x_46 = x_76;
goto block_49;
}
}
block_44:
{
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_mk_string_unchecked("error", 5, 5);
x_18 = l_Lean_Name_mkStr3(x_1, x_2, x_17);
lean_inc(x_18);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_isTracingEnabledFor___redArg(x_3, x_4, x_5, x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_20 = lean_apply_5(x_19, x_9, x_10, x_11, x_12, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_14);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
lean_inc(x_14);
x_28 = l_Lean_Exception_toMessageData(x_14);
x_29 = l_Lean_addTrace___redArg(x_3, x_4, x_6, x_7, x_18, x_28);
x_30 = lean_apply_5(x_29, x_9, x_10, x_11, x_12, x_27);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 0, x_14);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_14);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_14);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_20);
if (x_39 == 0)
{
return x_20;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_20, 0);
x_41 = lean_ctor_get(x_20, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_20);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_14);
lean_ctor_set(x_43, 1, x_15);
return x_43;
}
}
block_49:
{
uint8_t x_47; 
x_47 = l_Lean_Exception_isInterrupt(x_45);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = l_Lean_Exception_isRuntime(x_45);
x_14 = x_45;
x_15 = x_46;
x_16 = x_48;
goto block_44;
}
else
{
x_14 = x_45;
x_15 = x_46;
x_16 = x_47;
goto block_44;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0), 2, 0);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__1___boxed), 10, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
x_15 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_17 = l_instMonadEIO(lean_box(0));
x_18 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_20);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, lean_box(0));
x_31 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_31, 0, x_30);
x_32 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_32, 0, x_31);
lean_inc(x_32);
lean_inc(x_29);
lean_inc(x_26);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set(x_33, 1, x_15);
lean_ctor_set(x_33, 2, x_26);
lean_ctor_set(x_33, 3, x_29);
lean_ctor_set(x_33, 4, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_16);
x_35 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_37);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_26);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_29);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_43);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_45, 0, x_32);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_13);
lean_ctor_set(x_47, 2, x_42);
lean_ctor_set(x_47, 3, x_44);
lean_ctor_set(x_47, 4, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_14);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 0);
x_50 = l_StateRefT_x27_instMonadLift(lean_box(0), lean_box(0), lean_box(0));
x_51 = l_Lean_Core_instMonadTraceCoreM;
lean_inc(x_50);
x_52 = l_Lean_instMonadTraceOfMonadLift(lean_box(0), lean_box(0), x_50, x_51);
lean_inc(x_49);
x_53 = l_Lean_instMonadTraceOfMonadLift(lean_box(0), lean_box(0), x_49, x_52);
x_54 = lean_alloc_closure((void*)(l_ReaderT_instMonadFunctor___lam__0), 4, 0);
x_55 = l_Lean_Core_instMonadQuotationCoreM;
lean_inc(x_50);
lean_inc(x_54);
x_56 = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(x_54, x_50, x_55);
lean_inc(x_49);
x_57 = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(x_54, x_49, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_Meta_instAddMessageContextMetaM;
x_60 = lean_alloc_closure((void*)(l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed), 3, 0);
x_61 = l_Lean_instMonadOptionsOfMonadLift(lean_box(0), lean_box(0), x_50, x_60);
x_62 = l_Lean_instMonadOptionsOfMonadLift(lean_box(0), lean_box(0), x_49, x_61);
x_63 = l_Lean_instMonadAlwaysExceptEIO(lean_box(0));
x_64 = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(x_63);
x_65 = l_Lean_instMonadAlwaysExceptReaderT___redArg(x_64);
x_66 = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(x_65);
x_67 = l_Lean_instMonadAlwaysExceptReaderT___redArg(x_66);
x_68 = lean_mk_string_unchecked("Meta", 4, 4);
x_69 = lean_mk_string_unchecked("appBuilder", 10, 10);
lean_inc(x_58);
lean_inc(x_62);
lean_inc(x_53);
lean_inc(x_48);
lean_inc(x_69);
lean_inc(x_68);
x_70 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__2), 13, 8);
lean_closure_set(x_70, 0, x_68);
lean_closure_set(x_70, 1, x_69);
lean_closure_set(x_70, 2, x_48);
lean_closure_set(x_70, 3, x_53);
lean_closure_set(x_70, 4, x_62);
lean_closure_set(x_70, 5, x_58);
lean_closure_set(x_70, 6, x_59);
lean_closure_set(x_70, 7, x_5);
x_71 = l_Lean_Name_mkStr2(x_68, x_69);
x_72 = lean_box(1);
x_73 = lean_mk_string_unchecked("", 0, 0);
x_74 = lean_unbox(x_72);
x_75 = l_Lean_withTraceNode___redArg(x_48, x_53, x_58, x_59, x_62, x_67, x_11, x_71, x_12, x_70, x_74, x_73);
x_76 = lean_apply_5(x_75, x_6, x_7, x_8, x_9, x_10);
return x_76;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_MessageData_ofExpr(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_MessageData_ofExpr(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_mk_string_unchecked("", 0, 0);
x_10 = l_Lean_stringToMessageData(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_30; 
x_30 = lean_mk_string_unchecked("❌️", 6, 2);
x_11 = x_30;
goto block_29;
}
else
{
lean_object* x_31; 
x_31 = lean_mk_string_unchecked("✅️", 6, 2);
x_11 = x_31;
goto block_29;
}
block_29:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_12 = l_Lean_stringToMessageData(x_11);
lean_inc(x_10);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked(" f: ", 4, 4);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_MessageData_ofName(x_1);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_string_unchecked(", xs: ", 6, 6);
x_20 = l_Lean_stringToMessageData(x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_to_list(x_2);
x_23 = lean_box(0);
x_24 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_22, x_23);
x_25 = l_Lean_MessageData_ofList(x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_10);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_30; lean_object* x_31; lean_object* x_35; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_35 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_mk_string_unchecked("result", 6, 6);
x_39 = l_Lean_Name_mkStr3(x_1, x_2, x_38);
lean_inc(x_39);
x_40 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_39, x_4, x_5, x_6, x_7, x_37);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
uint8_t x_43; 
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_40, 0);
lean_dec(x_44);
lean_ctor_set(x_40, 0, x_36);
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_dec(x_40);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_dec(x_40);
lean_inc(x_36);
x_48 = l_Lean_MessageData_ofExpr(x_36);
x_49 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_39, x_48, x_4, x_5, x_6, x_7, x_47);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_36);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_36);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
if (lean_obj_tag(x_35) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_35;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_35, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_35, 1);
lean_inc(x_55);
lean_dec(x_35);
x_30 = x_54;
x_31 = x_55;
goto block_34;
}
}
block_29:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_mk_string_unchecked("error", 5, 5);
x_13 = l_Lean_Name_mkStr3(x_1, x_2, x_12);
lean_inc(x_13);
x_14 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_13, x_4, x_5, x_6, x_7, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_9);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
lean_inc(x_9);
x_22 = l_Lean_Exception_toMessageData(x_9);
x_23 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_13, x_22, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_9);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_9);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_10);
return x_28;
}
}
block_34:
{
uint8_t x_32; 
x_32 = l_Lean_Exception_isInterrupt(x_30);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Exception_isRuntime(x_30);
x_9 = x_30;
x_10 = x_31;
x_11 = x_33;
goto block_29;
}
else
{
x_9 = x_30;
x_10 = x_31;
x_11 = x_32;
goto block_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_mk_string_unchecked("Meta", 4, 4);
x_11 = lean_mk_string_unchecked("appBuilder", 10, 10);
lean_inc(x_11);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0___lam__1), 8, 3);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_3);
x_13 = l_Lean_Name_mkStr2(x_10, x_11);
x_14 = lean_box(1);
x_15 = lean_mk_string_unchecked("", 0, 0);
x_16 = lean_unbox(x_14);
x_17 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_13, x_9, x_12, x_16, x_15, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___lam__0___boxed), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___boxed), 8, 3);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_9);
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0(x_1, x_2, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkAppM___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_x27_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_mk_string_unchecked("", 0, 0);
x_10 = l_Lean_stringToMessageData(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_30; 
x_30 = lean_mk_string_unchecked("❌️", 6, 2);
x_11 = x_30;
goto block_29;
}
else
{
lean_object* x_31; 
x_31 = lean_mk_string_unchecked("✅️", 6, 2);
x_11 = x_31;
goto block_29;
}
block_29:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_12 = l_Lean_stringToMessageData(x_11);
lean_inc(x_10);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked(" f: ", 4, 4);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_MessageData_ofExpr(x_1);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_string_unchecked(", xs: ", 6, 6);
x_20 = l_Lean_stringToMessageData(x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_to_list(x_2);
x_23 = lean_box(0);
x_24 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_22, x_23);
x_25 = l_Lean_MessageData_ofList(x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_10);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_mk_string_unchecked("Meta", 4, 4);
x_11 = lean_mk_string_unchecked("appBuilder", 10, 10);
lean_inc(x_11);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0___lam__1), 8, 3);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_3);
x_13 = l_Lean_Name_mkStr2(x_10, x_11);
x_14 = lean_box(1);
x_15 = lean_mk_string_unchecked("", 0, 0);
x_16 = lean_unbox(x_14);
x_17 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_13, x_9, x_12, x_16, x_15, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed), 8, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___boxed), 8, 3);
lean_closure_set(x_13, 0, lean_box(0));
lean_closure_set(x_13, 1, x_11);
lean_closure_set(x_13, 2, x_12);
x_14 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_x27_spec__0(x_1, x_2, x_13, x_3, x_4, x_5, x_6, x_10);
return x_14;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_x27_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_12) == 0)
{
x_5 = x_4;
goto block_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_array_push(x_4, x_13);
x_5 = x_14;
goto block_10;
}
}
else
{
return x_4;
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_7) == 7)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 2);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
lean_dec(x_7);
x_17 = lean_array_get_size(x_2);
x_18 = lean_nat_dec_lt(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
x_19 = lean_mk_string_unchecked("mkAppOptM", 9, 9);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_20, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_array_get_size(x_4);
x_23 = lean_expr_instantiate_rev_range(x_14, x_5, x_22, x_4);
lean_dec(x_22);
lean_dec(x_14);
x_24 = lean_array_fget(x_2, x_3);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_box(x_16);
if (lean_obj_tag(x_25) == 3)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_27 = lean_box(1);
x_28 = lean_unbox(x_27);
lean_inc(x_8);
x_29 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_26, x_28, x_13, x_8, x_9, x_10, x_11, x_12);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_3, x_32);
lean_dec(x_3);
lean_inc(x_30);
x_34 = lean_array_push(x_4, x_30);
x_35 = l_Lean_Expr_mvarId_x21(x_30);
lean_dec(x_30);
x_36 = lean_array_push(x_6, x_35);
x_3 = x_33;
x_4 = x_34;
x_6 = x_36;
x_7 = x_15;
x_12 = x_31;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_25);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_23);
x_39 = lean_box(0);
x_40 = lean_unbox(x_39);
lean_inc(x_8);
x_41 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_38, x_40, x_13, x_8, x_9, x_10, x_11, x_12);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_3, x_44);
lean_dec(x_3);
x_46 = lean_array_push(x_4, x_42);
x_3 = x_45;
x_4 = x_46;
x_7 = x_15;
x_12 = x_43;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_13);
x_48 = lean_ctor_get(x_24, 0);
lean_inc(x_48);
lean_dec(x_24);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_48);
x_49 = lean_infer_type(x_48, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_52 = l_Lean_Meta_isExprDefEq(x_23, x_50, x_8, x_9, x_10, x_11, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l_Lean_mkAppN(x_1, x_4);
lean_dec(x_4);
x_57 = l_Lean_Meta_throwAppTypeMismatch___redArg(x_56, x_48, x_8, x_9, x_10, x_11, x_55);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_dec(x_52);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_3, x_59);
lean_dec(x_3);
x_61 = lean_array_push(x_4, x_48);
x_3 = x_60;
x_4 = x_61;
x_7 = x_15;
x_12 = x_58;
goto _start;
}
}
else
{
uint8_t x_63; 
lean_dec(x_48);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_52);
if (x_63 == 0)
{
return x_52;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_52, 0);
x_65 = lean_ctor_get(x_52, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_52);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_dec(x_48);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_49;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_array_get_size(x_4);
x_68 = lean_expr_instantiate_rev_range(x_7, x_5, x_67, x_4);
lean_dec(x_5);
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_69 = l_Lean_Meta_whnfD(x_68, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
x_73 = l_Lean_Expr_isForall(x_70);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
lean_dec(x_70);
lean_dec(x_67);
x_74 = lean_array_get_size(x_2);
x_75 = lean_nat_dec_eq(x_3, x_74);
lean_dec(x_3);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_99; uint8_t x_100; 
lean_dec(x_6);
lean_dec(x_4);
x_76 = lean_unsigned_to_nat(0u);
x_99 = lean_mk_empty_array_with_capacity(x_76);
x_100 = lean_nat_dec_lt(x_76, x_74);
if (x_100 == 0)
{
lean_dec(x_74);
x_77 = x_99;
goto block_98;
}
else
{
uint8_t x_101; 
x_101 = lean_nat_dec_le(x_74, x_74);
if (x_101 == 0)
{
lean_dec(x_74);
x_77 = x_99;
goto block_98;
}
else
{
size_t x_102; size_t x_103; lean_object* x_104; 
x_102 = lean_usize_of_nat(x_76);
x_103 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_104 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(x_2, x_102, x_103, x_99);
x_77 = x_104;
goto block_98;
}
}
block_98:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_78 = lean_mk_string_unchecked("mkAppOptM", 9, 9);
x_79 = l_Lean_Name_mkStr1(x_78);
x_80 = lean_mk_string_unchecked("too many arguments provided to", 30, 30);
x_81 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = l_Lean_MessageData_ofFormat(x_81);
x_83 = l_Lean_indentExpr(x_1);
if (lean_is_scalar(x_72)) {
 x_84 = lean_alloc_ctor(7, 2, 0);
} else {
 x_84 = x_72;
 lean_ctor_set_tag(x_84, 7);
}
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_box(1);
x_86 = l_Lean_MessageData_ofFormat(x_85);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_mk_string_unchecked("arguments", 9, 9);
x_89 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = l_Lean_MessageData_ofFormat(x_89);
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_87);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_mk_string_unchecked("#[", 2, 2);
x_93 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = l_Lean_MessageData_ofFormat(x_93);
x_95 = l_Lean_MessageData_arrayExpr_toMessageData(x_77, x_76, x_94);
lean_dec(x_77);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_91);
lean_ctor_set(x_96, 1, x_95);
x_97 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_79, x_96, x_8, x_9, x_10, x_11, x_71);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_97;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_74);
lean_dec(x_72);
x_105 = lean_mk_string_unchecked("mkAppOptM", 9, 9);
x_106 = l_Lean_Name_mkStr1(x_105);
x_107 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_106, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_71);
lean_dec(x_6);
lean_dec(x_4);
return x_107;
}
}
else
{
lean_dec(x_72);
x_5 = x_67;
x_7 = x_70;
x_12 = x_71;
goto _start;
}
}
else
{
lean_dec(x_67);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_6 = x_1;
} else {
 lean_dec_ref(x_1);
 x_6 = lean_box(0);
}
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_mk_string_unchecked("<not-available>", 15, 15);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_MessageData_ofFormat(x_12);
x_7 = x_13;
goto block_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
lean_dec(x_4);
x_15 = l_Lean_MessageData_ofExpr(x_14);
x_7 = x_15;
goto block_10;
}
block_10:
{
lean_object* x_8; 
if (lean_is_scalar(x_6)) {
 x_8 = lean_alloc_ctor(1, 2, 0);
} else {
 x_8 = x_6;
}
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_1 = x_5;
x_2 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_mk_string_unchecked("", 0, 0);
x_10 = l_Lean_stringToMessageData(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_30; 
x_30 = lean_mk_string_unchecked("❌️", 6, 2);
x_11 = x_30;
goto block_29;
}
else
{
lean_object* x_31; 
x_31 = lean_mk_string_unchecked("✅️", 6, 2);
x_11 = x_31;
goto block_29;
}
block_29:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_12 = l_Lean_stringToMessageData(x_11);
lean_inc(x_10);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked(" f: ", 4, 4);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_MessageData_ofName(x_1);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_string_unchecked(", xs: ", 6, 6);
x_20 = l_Lean_stringToMessageData(x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_to_list(x_2);
x_23 = lean_box(0);
x_24 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_spec__0_spec__0(x_22, x_23);
x_25 = l_Lean_MessageData_ofList(x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_10);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_mk_string_unchecked("Meta", 4, 4);
x_11 = lean_mk_string_unchecked("appBuilder", 10, 10);
lean_inc(x_11);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0___lam__1), 8, 3);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_3);
x_13 = l_Lean_Name_mkStr2(x_10, x_11);
x_14 = lean_box(1);
x_15 = lean_mk_string_unchecked("", 0, 0);
x_16 = lean_unbox(x_14);
x_17 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_13, x_9, x_12, x_16, x_15, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_mk_empty_array_with_capacity(x_13);
lean_inc(x_14);
x_15 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(x_11, x_2, x_13, x_14, x_13, x_14, x_12, x_3, x_4, x_5, x_6, x_10);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppOptM___lam__0___boxed), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___boxed), 8, 3);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_9);
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_spec__0(x_1, x_2, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkAppOptM___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_x27_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_mk_string_unchecked("", 0, 0);
x_10 = l_Lean_stringToMessageData(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_30; 
x_30 = lean_mk_string_unchecked("❌️", 6, 2);
x_11 = x_30;
goto block_29;
}
else
{
lean_object* x_31; 
x_31 = lean_mk_string_unchecked("✅️", 6, 2);
x_11 = x_31;
goto block_29;
}
block_29:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_12 = l_Lean_stringToMessageData(x_11);
lean_inc(x_10);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked(" f: ", 4, 4);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_MessageData_ofExpr(x_1);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_string_unchecked(", xs: ", 6, 6);
x_20 = l_Lean_stringToMessageData(x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_to_list(x_2);
x_23 = lean_box(0);
x_24 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_spec__0_spec__0(x_22, x_23);
x_25 = l_Lean_MessageData_ofList(x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_10);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_mk_string_unchecked("Meta", 4, 4);
x_11 = lean_mk_string_unchecked("appBuilder", 10, 10);
lean_inc(x_11);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0___lam__1), 8, 3);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_3);
x_13 = l_Lean_Name_mkStr2(x_10, x_11);
x_14 = lean_box(1);
x_15 = lean_mk_string_unchecked("", 0, 0);
x_16 = lean_unbox(x_14);
x_17 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_13, x_9, x_12, x_16, x_15, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_mk_empty_array_with_capacity(x_11);
lean_inc(x_12);
lean_inc(x_2);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed), 12, 7);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, x_11);
lean_closure_set(x_13, 5, x_12);
lean_closure_set(x_13, 6, x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___boxed), 8, 3);
lean_closure_set(x_15, 0, lean_box(0));
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_14);
x_16 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_x27_spec__0(x_1, x_2, x_15, x_3, x_4, x_5, x_6, x_10);
return x_16;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppOptM_x27_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_mk_string_unchecked("ndrec", 5, 5);
x_10 = l_Lean_Name_mkStr2(x_1, x_9);
x_11 = lean_mk_string_unchecked("invalid motive", 14, 14);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_MessageData_ofFormat(x_12);
x_14 = l_Lean_indentExpr(x_2);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_10, x_15, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_mk_string_unchecked("Eq", 2, 2);
x_10 = lean_mk_string_unchecked("refl", 4, 4);
lean_inc(x_9);
x_11 = l_Lean_Name_mkStr2(x_9, x_10);
x_12 = l_Lean_Expr_isAppOf(x_3, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_9);
x_17 = l_Lean_Name_mkStr1(x_9);
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Expr_isAppOfArity(x_15, x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_mk_string_unchecked("ndrec", 5, 5);
x_21 = l_Lean_Name_mkStr2(x_9, x_20);
x_22 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_MessageData_ofFormat(x_23);
x_25 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_3, x_15);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_25);
lean_ctor_set(x_13, 0, x_24);
x_26 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_21, x_13, x_4, x_5, x_6, x_7, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l_Lean_Expr_appFn_x21(x_15);
x_28 = l_Lean_Expr_appFn_x21(x_27);
x_29 = l_Lean_Expr_appArg_x21(x_28);
lean_dec(x_28);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_29);
x_30 = l_Lean_Meta_getLevel(x_29, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_33 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_4, x_5, x_6, x_7, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 7)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 2);
lean_inc(x_35);
switch (lean_obj_tag(x_35)) {
case 0:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
lean_dec(x_35);
x_41 = l_Lean_Expr_bvar___override(x_40);
x_42 = l_Lean_Expr_forallE___override(x_37, x_38, x_41, x_39);
x_43 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_42, x_4, x_5, x_6, x_7, x_36);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_42);
return x_43;
}
case 1:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_dec(x_33);
x_45 = lean_ctor_get(x_34, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
x_47 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
lean_dec(x_35);
x_49 = l_Lean_Expr_fvar___override(x_48);
x_50 = l_Lean_Expr_forallE___override(x_45, x_46, x_49, x_47);
x_51 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_50, x_4, x_5, x_6, x_7, x_44);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_50);
return x_51;
}
case 2:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_ctor_get(x_33, 1);
lean_inc(x_52);
lean_dec(x_33);
x_53 = lean_ctor_get(x_34, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_34, 1);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_56 = lean_ctor_get(x_35, 0);
lean_inc(x_56);
lean_dec(x_35);
x_57 = l_Lean_Expr_mvar___override(x_56);
x_58 = l_Lean_Expr_forallE___override(x_53, x_54, x_57, x_55);
x_59 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_58, x_4, x_5, x_6, x_7, x_52);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_58);
return x_59;
}
case 3:
{
uint8_t x_60; 
lean_dec(x_34);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_33);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_61 = lean_ctor_get(x_33, 0);
lean_dec(x_61);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
lean_dec(x_35);
x_63 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
x_64 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
x_65 = lean_mk_string_unchecked("ndrec", 5, 5);
x_66 = l_Lean_Name_mkStr2(x_9, x_65);
x_67 = lean_box(0);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_67);
lean_ctor_set(x_13, 0, x_31);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_13);
x_69 = l_Lean_Expr_const___override(x_66, x_68);
x_70 = lean_unsigned_to_nat(6u);
x_71 = lean_mk_empty_array_with_capacity(x_70);
x_72 = lean_array_push(x_71, x_29);
x_73 = lean_array_push(x_72, x_63);
x_74 = lean_array_push(x_73, x_1);
x_75 = lean_array_push(x_74, x_2);
x_76 = lean_array_push(x_75, x_64);
x_77 = lean_array_push(x_76, x_3);
x_78 = l_Lean_mkAppN(x_69, x_77);
lean_dec(x_77);
lean_ctor_set(x_33, 0, x_78);
return x_33;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_79 = lean_ctor_get(x_33, 1);
lean_inc(x_79);
lean_dec(x_33);
x_80 = lean_ctor_get(x_35, 0);
lean_inc(x_80);
lean_dec(x_35);
x_81 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
x_82 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
x_83 = lean_mk_string_unchecked("ndrec", 5, 5);
x_84 = l_Lean_Name_mkStr2(x_9, x_83);
x_85 = lean_box(0);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_85);
lean_ctor_set(x_13, 0, x_31);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_13);
x_87 = l_Lean_Expr_const___override(x_84, x_86);
x_88 = lean_unsigned_to_nat(6u);
x_89 = lean_mk_empty_array_with_capacity(x_88);
x_90 = lean_array_push(x_89, x_29);
x_91 = lean_array_push(x_90, x_81);
x_92 = lean_array_push(x_91, x_1);
x_93 = lean_array_push(x_92, x_2);
x_94 = lean_array_push(x_93, x_82);
x_95 = lean_array_push(x_94, x_3);
x_96 = l_Lean_mkAppN(x_87, x_95);
lean_dec(x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_79);
return x_97;
}
}
case 4:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_98 = lean_ctor_get(x_33, 1);
lean_inc(x_98);
lean_dec(x_33);
x_99 = lean_ctor_get(x_34, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_34, 1);
lean_inc(x_100);
x_101 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_102 = lean_ctor_get(x_35, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_35, 1);
lean_inc(x_103);
lean_dec(x_35);
x_104 = l_Lean_Expr_const___override(x_102, x_103);
x_105 = l_Lean_Expr_forallE___override(x_99, x_100, x_104, x_101);
x_106 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_105, x_4, x_5, x_6, x_7, x_98);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_105);
return x_106;
}
case 5:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_107 = lean_ctor_get(x_33, 1);
lean_inc(x_107);
lean_dec(x_33);
x_108 = lean_ctor_get(x_34, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_34, 1);
lean_inc(x_109);
x_110 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_111 = lean_ctor_get(x_35, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_35, 1);
lean_inc(x_112);
lean_dec(x_35);
x_113 = l_Lean_Expr_app___override(x_111, x_112);
x_114 = l_Lean_Expr_forallE___override(x_108, x_109, x_113, x_110);
x_115 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_114, x_4, x_5, x_6, x_7, x_107);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_114);
return x_115;
}
case 6:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_116 = lean_ctor_get(x_33, 1);
lean_inc(x_116);
lean_dec(x_33);
x_117 = lean_ctor_get(x_34, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_34, 1);
lean_inc(x_118);
x_119 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_120 = lean_ctor_get(x_35, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_35, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_35, 2);
lean_inc(x_122);
x_123 = lean_ctor_get_uint8(x_35, sizeof(void*)*3 + 8);
lean_dec(x_35);
x_124 = l_Lean_Expr_lam___override(x_120, x_121, x_122, x_123);
x_125 = l_Lean_Expr_forallE___override(x_117, x_118, x_124, x_119);
x_126 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_125, x_4, x_5, x_6, x_7, x_116);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_125);
return x_126;
}
case 7:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_127 = lean_ctor_get(x_33, 1);
lean_inc(x_127);
lean_dec(x_33);
x_128 = lean_ctor_get(x_34, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_34, 1);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_131 = lean_ctor_get(x_35, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_35, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_35, 2);
lean_inc(x_133);
x_134 = lean_ctor_get_uint8(x_35, sizeof(void*)*3 + 8);
lean_dec(x_35);
x_135 = l_Lean_Expr_forallE___override(x_131, x_132, x_133, x_134);
x_136 = l_Lean_Expr_forallE___override(x_128, x_129, x_135, x_130);
x_137 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_136, x_4, x_5, x_6, x_7, x_127);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_136);
return x_137;
}
case 8:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_138 = lean_ctor_get(x_33, 1);
lean_inc(x_138);
lean_dec(x_33);
x_139 = lean_ctor_get(x_34, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_34, 1);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_142 = lean_ctor_get(x_35, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_35, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_35, 2);
lean_inc(x_144);
x_145 = lean_ctor_get(x_35, 3);
lean_inc(x_145);
x_146 = lean_ctor_get_uint8(x_35, sizeof(void*)*4 + 8);
lean_dec(x_35);
x_147 = l_Lean_Expr_letE___override(x_142, x_143, x_144, x_145, x_146);
x_148 = l_Lean_Expr_forallE___override(x_139, x_140, x_147, x_141);
x_149 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_148, x_4, x_5, x_6, x_7, x_138);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_148);
return x_149;
}
case 9:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_150 = lean_ctor_get(x_33, 1);
lean_inc(x_150);
lean_dec(x_33);
x_151 = lean_ctor_get(x_34, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_34, 1);
lean_inc(x_152);
x_153 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_154 = lean_ctor_get(x_35, 0);
lean_inc(x_154);
lean_dec(x_35);
x_155 = l_Lean_Expr_lit___override(x_154);
x_156 = l_Lean_Expr_forallE___override(x_151, x_152, x_155, x_153);
x_157 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_156, x_4, x_5, x_6, x_7, x_150);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_156);
return x_157;
}
case 10:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_158 = lean_ctor_get(x_33, 1);
lean_inc(x_158);
lean_dec(x_33);
x_159 = lean_ctor_get(x_34, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_34, 1);
lean_inc(x_160);
x_161 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_162 = lean_ctor_get(x_35, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_35, 1);
lean_inc(x_163);
lean_dec(x_35);
x_164 = l_Lean_Expr_mdata___override(x_162, x_163);
x_165 = l_Lean_Expr_forallE___override(x_159, x_160, x_164, x_161);
x_166 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_165, x_4, x_5, x_6, x_7, x_158);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_165);
return x_166;
}
default: 
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_167 = lean_ctor_get(x_33, 1);
lean_inc(x_167);
lean_dec(x_33);
x_168 = lean_ctor_get(x_34, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_34, 1);
lean_inc(x_169);
x_170 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_171 = lean_ctor_get(x_35, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_35, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_35, 2);
lean_inc(x_173);
lean_dec(x_35);
x_174 = l_Lean_Expr_proj___override(x_171, x_172, x_173);
x_175 = l_Lean_Expr_forallE___override(x_168, x_169, x_174, x_170);
x_176 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_175, x_4, x_5, x_6, x_7, x_167);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_175);
return x_176;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_177 = lean_ctor_get(x_33, 1);
lean_inc(x_177);
lean_dec(x_33);
x_178 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_34, x_4, x_5, x_6, x_7, x_177);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_34);
return x_178;
}
}
else
{
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_33;
}
}
else
{
uint8_t x_179; 
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_179 = !lean_is_exclusive(x_30);
if (x_179 == 0)
{
return x_30;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_30, 0);
x_181 = lean_ctor_get(x_30, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_30);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_183 = lean_ctor_get(x_13, 0);
x_184 = lean_ctor_get(x_13, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_13);
lean_inc(x_9);
x_185 = l_Lean_Name_mkStr1(x_9);
x_186 = lean_unsigned_to_nat(3u);
x_187 = l_Lean_Expr_isAppOfArity(x_183, x_185, x_186);
lean_dec(x_185);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_2);
lean_dec(x_1);
x_188 = lean_mk_string_unchecked("ndrec", 5, 5);
x_189 = l_Lean_Name_mkStr2(x_9, x_188);
x_190 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_191 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_191, 0, x_190);
x_192 = l_Lean_MessageData_ofFormat(x_191);
x_193 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_3, x_183);
x_194 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_195 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_189, x_194, x_4, x_5, x_6, x_7, x_184);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_195;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_196 = l_Lean_Expr_appFn_x21(x_183);
x_197 = l_Lean_Expr_appFn_x21(x_196);
x_198 = l_Lean_Expr_appArg_x21(x_197);
lean_dec(x_197);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_198);
x_199 = l_Lean_Meta_getLevel(x_198, x_4, x_5, x_6, x_7, x_184);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_202 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_4, x_5, x_6, x_7, x_201);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
if (lean_obj_tag(x_203) == 7)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_203, 2);
lean_inc(x_204);
switch (lean_obj_tag(x_204)) {
case 0:
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_183);
lean_dec(x_3);
lean_dec(x_2);
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
lean_dec(x_202);
x_206 = lean_ctor_get(x_203, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_203, 1);
lean_inc(x_207);
x_208 = lean_ctor_get_uint8(x_203, sizeof(void*)*3 + 8);
lean_dec(x_203);
x_209 = lean_ctor_get(x_204, 0);
lean_inc(x_209);
lean_dec(x_204);
x_210 = l_Lean_Expr_bvar___override(x_209);
x_211 = l_Lean_Expr_forallE___override(x_206, x_207, x_210, x_208);
x_212 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_211, x_4, x_5, x_6, x_7, x_205);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_211);
return x_212;
}
case 1:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_183);
lean_dec(x_3);
lean_dec(x_2);
x_213 = lean_ctor_get(x_202, 1);
lean_inc(x_213);
lean_dec(x_202);
x_214 = lean_ctor_get(x_203, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_203, 1);
lean_inc(x_215);
x_216 = lean_ctor_get_uint8(x_203, sizeof(void*)*3 + 8);
lean_dec(x_203);
x_217 = lean_ctor_get(x_204, 0);
lean_inc(x_217);
lean_dec(x_204);
x_218 = l_Lean_Expr_fvar___override(x_217);
x_219 = l_Lean_Expr_forallE___override(x_214, x_215, x_218, x_216);
x_220 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_219, x_4, x_5, x_6, x_7, x_213);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_219);
return x_220;
}
case 2:
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_183);
lean_dec(x_3);
lean_dec(x_2);
x_221 = lean_ctor_get(x_202, 1);
lean_inc(x_221);
lean_dec(x_202);
x_222 = lean_ctor_get(x_203, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_203, 1);
lean_inc(x_223);
x_224 = lean_ctor_get_uint8(x_203, sizeof(void*)*3 + 8);
lean_dec(x_203);
x_225 = lean_ctor_get(x_204, 0);
lean_inc(x_225);
lean_dec(x_204);
x_226 = l_Lean_Expr_mvar___override(x_225);
x_227 = l_Lean_Expr_forallE___override(x_222, x_223, x_226, x_224);
x_228 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_227, x_4, x_5, x_6, x_7, x_221);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_227);
return x_228;
}
case 3:
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_203);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_229 = lean_ctor_get(x_202, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_230 = x_202;
} else {
 lean_dec_ref(x_202);
 x_230 = lean_box(0);
}
x_231 = lean_ctor_get(x_204, 0);
lean_inc(x_231);
lean_dec(x_204);
x_232 = l_Lean_Expr_appArg_x21(x_196);
lean_dec(x_196);
x_233 = l_Lean_Expr_appArg_x21(x_183);
lean_dec(x_183);
x_234 = lean_mk_string_unchecked("ndrec", 5, 5);
x_235 = l_Lean_Name_mkStr2(x_9, x_234);
x_236 = lean_box(0);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_200);
lean_ctor_set(x_237, 1, x_236);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_231);
lean_ctor_set(x_238, 1, x_237);
x_239 = l_Lean_Expr_const___override(x_235, x_238);
x_240 = lean_unsigned_to_nat(6u);
x_241 = lean_mk_empty_array_with_capacity(x_240);
x_242 = lean_array_push(x_241, x_198);
x_243 = lean_array_push(x_242, x_232);
x_244 = lean_array_push(x_243, x_1);
x_245 = lean_array_push(x_244, x_2);
x_246 = lean_array_push(x_245, x_233);
x_247 = lean_array_push(x_246, x_3);
x_248 = l_Lean_mkAppN(x_239, x_247);
lean_dec(x_247);
if (lean_is_scalar(x_230)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_230;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_229);
return x_249;
}
case 4:
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_183);
lean_dec(x_3);
lean_dec(x_2);
x_250 = lean_ctor_get(x_202, 1);
lean_inc(x_250);
lean_dec(x_202);
x_251 = lean_ctor_get(x_203, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_203, 1);
lean_inc(x_252);
x_253 = lean_ctor_get_uint8(x_203, sizeof(void*)*3 + 8);
lean_dec(x_203);
x_254 = lean_ctor_get(x_204, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_204, 1);
lean_inc(x_255);
lean_dec(x_204);
x_256 = l_Lean_Expr_const___override(x_254, x_255);
x_257 = l_Lean_Expr_forallE___override(x_251, x_252, x_256, x_253);
x_258 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_257, x_4, x_5, x_6, x_7, x_250);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_257);
return x_258;
}
case 5:
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_183);
lean_dec(x_3);
lean_dec(x_2);
x_259 = lean_ctor_get(x_202, 1);
lean_inc(x_259);
lean_dec(x_202);
x_260 = lean_ctor_get(x_203, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_203, 1);
lean_inc(x_261);
x_262 = lean_ctor_get_uint8(x_203, sizeof(void*)*3 + 8);
lean_dec(x_203);
x_263 = lean_ctor_get(x_204, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_204, 1);
lean_inc(x_264);
lean_dec(x_204);
x_265 = l_Lean_Expr_app___override(x_263, x_264);
x_266 = l_Lean_Expr_forallE___override(x_260, x_261, x_265, x_262);
x_267 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_266, x_4, x_5, x_6, x_7, x_259);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_266);
return x_267;
}
case 6:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_183);
lean_dec(x_3);
lean_dec(x_2);
x_268 = lean_ctor_get(x_202, 1);
lean_inc(x_268);
lean_dec(x_202);
x_269 = lean_ctor_get(x_203, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_203, 1);
lean_inc(x_270);
x_271 = lean_ctor_get_uint8(x_203, sizeof(void*)*3 + 8);
lean_dec(x_203);
x_272 = lean_ctor_get(x_204, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_204, 1);
lean_inc(x_273);
x_274 = lean_ctor_get(x_204, 2);
lean_inc(x_274);
x_275 = lean_ctor_get_uint8(x_204, sizeof(void*)*3 + 8);
lean_dec(x_204);
x_276 = l_Lean_Expr_lam___override(x_272, x_273, x_274, x_275);
x_277 = l_Lean_Expr_forallE___override(x_269, x_270, x_276, x_271);
x_278 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_277, x_4, x_5, x_6, x_7, x_268);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_277);
return x_278;
}
case 7:
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_183);
lean_dec(x_3);
lean_dec(x_2);
x_279 = lean_ctor_get(x_202, 1);
lean_inc(x_279);
lean_dec(x_202);
x_280 = lean_ctor_get(x_203, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_203, 1);
lean_inc(x_281);
x_282 = lean_ctor_get_uint8(x_203, sizeof(void*)*3 + 8);
lean_dec(x_203);
x_283 = lean_ctor_get(x_204, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_204, 1);
lean_inc(x_284);
x_285 = lean_ctor_get(x_204, 2);
lean_inc(x_285);
x_286 = lean_ctor_get_uint8(x_204, sizeof(void*)*3 + 8);
lean_dec(x_204);
x_287 = l_Lean_Expr_forallE___override(x_283, x_284, x_285, x_286);
x_288 = l_Lean_Expr_forallE___override(x_280, x_281, x_287, x_282);
x_289 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_288, x_4, x_5, x_6, x_7, x_279);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_288);
return x_289;
}
case 8:
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_183);
lean_dec(x_3);
lean_dec(x_2);
x_290 = lean_ctor_get(x_202, 1);
lean_inc(x_290);
lean_dec(x_202);
x_291 = lean_ctor_get(x_203, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_203, 1);
lean_inc(x_292);
x_293 = lean_ctor_get_uint8(x_203, sizeof(void*)*3 + 8);
lean_dec(x_203);
x_294 = lean_ctor_get(x_204, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_204, 1);
lean_inc(x_295);
x_296 = lean_ctor_get(x_204, 2);
lean_inc(x_296);
x_297 = lean_ctor_get(x_204, 3);
lean_inc(x_297);
x_298 = lean_ctor_get_uint8(x_204, sizeof(void*)*4 + 8);
lean_dec(x_204);
x_299 = l_Lean_Expr_letE___override(x_294, x_295, x_296, x_297, x_298);
x_300 = l_Lean_Expr_forallE___override(x_291, x_292, x_299, x_293);
x_301 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_300, x_4, x_5, x_6, x_7, x_290);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_300);
return x_301;
}
case 9:
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_183);
lean_dec(x_3);
lean_dec(x_2);
x_302 = lean_ctor_get(x_202, 1);
lean_inc(x_302);
lean_dec(x_202);
x_303 = lean_ctor_get(x_203, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_203, 1);
lean_inc(x_304);
x_305 = lean_ctor_get_uint8(x_203, sizeof(void*)*3 + 8);
lean_dec(x_203);
x_306 = lean_ctor_get(x_204, 0);
lean_inc(x_306);
lean_dec(x_204);
x_307 = l_Lean_Expr_lit___override(x_306);
x_308 = l_Lean_Expr_forallE___override(x_303, x_304, x_307, x_305);
x_309 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_308, x_4, x_5, x_6, x_7, x_302);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_308);
return x_309;
}
case 10:
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_183);
lean_dec(x_3);
lean_dec(x_2);
x_310 = lean_ctor_get(x_202, 1);
lean_inc(x_310);
lean_dec(x_202);
x_311 = lean_ctor_get(x_203, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_203, 1);
lean_inc(x_312);
x_313 = lean_ctor_get_uint8(x_203, sizeof(void*)*3 + 8);
lean_dec(x_203);
x_314 = lean_ctor_get(x_204, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_204, 1);
lean_inc(x_315);
lean_dec(x_204);
x_316 = l_Lean_Expr_mdata___override(x_314, x_315);
x_317 = l_Lean_Expr_forallE___override(x_311, x_312, x_316, x_313);
x_318 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_317, x_4, x_5, x_6, x_7, x_310);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_317);
return x_318;
}
default: 
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_183);
lean_dec(x_3);
lean_dec(x_2);
x_319 = lean_ctor_get(x_202, 1);
lean_inc(x_319);
lean_dec(x_202);
x_320 = lean_ctor_get(x_203, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_203, 1);
lean_inc(x_321);
x_322 = lean_ctor_get_uint8(x_203, sizeof(void*)*3 + 8);
lean_dec(x_203);
x_323 = lean_ctor_get(x_204, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_204, 1);
lean_inc(x_324);
x_325 = lean_ctor_get(x_204, 2);
lean_inc(x_325);
lean_dec(x_204);
x_326 = l_Lean_Expr_proj___override(x_323, x_324, x_325);
x_327 = l_Lean_Expr_forallE___override(x_320, x_321, x_326, x_322);
x_328 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_327, x_4, x_5, x_6, x_7, x_319);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_327);
return x_328;
}
}
}
else
{
lean_object* x_329; lean_object* x_330; 
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_183);
lean_dec(x_3);
lean_dec(x_2);
x_329 = lean_ctor_get(x_202, 1);
lean_inc(x_329);
lean_dec(x_202);
x_330 = l_Lean_Meta_mkEqNDRec___lam__0(x_9, x_1, x_203, x_4, x_5, x_6, x_7, x_329);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_203);
return x_330;
}
}
else
{
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_183);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_202;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_183);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_331 = lean_ctor_get(x_199, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_199, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_333 = x_199;
} else {
 lean_dec_ref(x_199);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_331);
lean_ctor_set(x_334, 1, x_332);
return x_334;
}
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
else
{
lean_object* x_335; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_2);
lean_ctor_set(x_335, 1, x_8);
return x_335;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkEqNDRec___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_mk_string_unchecked("rec", 3, 3);
x_10 = l_Lean_Name_mkStr2(x_1, x_9);
x_11 = lean_mk_string_unchecked("invalid motive", 14, 14);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_MessageData_ofFormat(x_12);
x_14 = l_Lean_indentExpr(x_2);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_10, x_15, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_mk_string_unchecked("Eq", 2, 2);
x_10 = lean_mk_string_unchecked("refl", 4, 4);
lean_inc(x_9);
x_11 = l_Lean_Name_mkStr2(x_9, x_10);
x_12 = l_Lean_Expr_isAppOf(x_3, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_9);
x_17 = l_Lean_Name_mkStr1(x_9);
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Expr_isAppOfArity(x_15, x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_mk_string_unchecked("rec", 3, 3);
x_21 = l_Lean_Name_mkStr2(x_9, x_20);
x_22 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_MessageData_ofFormat(x_23);
x_25 = l_Lean_indentExpr(x_3);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_25);
lean_ctor_set(x_13, 0, x_24);
x_26 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_21, x_13, x_4, x_5, x_6, x_7, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l_Lean_Expr_appFn_x21(x_15);
x_28 = l_Lean_Expr_appFn_x21(x_27);
x_29 = l_Lean_Expr_appArg_x21(x_28);
lean_dec(x_28);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_29);
x_30 = l_Lean_Meta_getLevel(x_29, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_33 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_4, x_5, x_6, x_7, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 7)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 2);
lean_inc(x_35);
switch (lean_obj_tag(x_35)) {
case 0:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
lean_dec(x_35);
x_41 = l_Lean_Expr_bvar___override(x_40);
x_42 = l_Lean_Expr_forallE___override(x_37, x_38, x_41, x_39);
x_43 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_42, x_4, x_5, x_6, x_7, x_36);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_42);
return x_43;
}
case 1:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_dec(x_33);
x_45 = lean_ctor_get(x_34, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
x_47 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
lean_dec(x_35);
x_49 = l_Lean_Expr_fvar___override(x_48);
x_50 = l_Lean_Expr_forallE___override(x_45, x_46, x_49, x_47);
x_51 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_50, x_4, x_5, x_6, x_7, x_44);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_50);
return x_51;
}
case 2:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_ctor_get(x_33, 1);
lean_inc(x_52);
lean_dec(x_33);
x_53 = lean_ctor_get(x_34, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_34, 1);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_56 = lean_ctor_get(x_35, 0);
lean_inc(x_56);
lean_dec(x_35);
x_57 = l_Lean_Expr_mvar___override(x_56);
x_58 = l_Lean_Expr_forallE___override(x_53, x_54, x_57, x_55);
x_59 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_58, x_4, x_5, x_6, x_7, x_52);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_58);
return x_59;
}
case 3:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_60 = lean_ctor_get(x_33, 1);
lean_inc(x_60);
lean_dec(x_33);
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_34, 1);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_64 = lean_ctor_get(x_35, 0);
lean_inc(x_64);
lean_dec(x_35);
x_65 = l_Lean_Expr_sort___override(x_64);
x_66 = l_Lean_Expr_forallE___override(x_61, x_62, x_65, x_63);
x_67 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_66, x_4, x_5, x_6, x_7, x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_66);
return x_67;
}
case 4:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_68 = lean_ctor_get(x_33, 1);
lean_inc(x_68);
lean_dec(x_33);
x_69 = lean_ctor_get(x_34, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_34, 1);
lean_inc(x_70);
x_71 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_72 = lean_ctor_get(x_35, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_35, 1);
lean_inc(x_73);
lean_dec(x_35);
x_74 = l_Lean_Expr_const___override(x_72, x_73);
x_75 = l_Lean_Expr_forallE___override(x_69, x_70, x_74, x_71);
x_76 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_75, x_4, x_5, x_6, x_7, x_68);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_75);
return x_76;
}
case 5:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_77 = lean_ctor_get(x_33, 1);
lean_inc(x_77);
lean_dec(x_33);
x_78 = lean_ctor_get(x_34, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_34, 1);
lean_inc(x_79);
x_80 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_81 = lean_ctor_get(x_35, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_35, 1);
lean_inc(x_82);
lean_dec(x_35);
x_83 = l_Lean_Expr_app___override(x_81, x_82);
x_84 = l_Lean_Expr_forallE___override(x_78, x_79, x_83, x_80);
x_85 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_84, x_4, x_5, x_6, x_7, x_77);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_84);
return x_85;
}
case 6:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_86 = lean_ctor_get(x_33, 1);
lean_inc(x_86);
lean_dec(x_33);
x_87 = lean_ctor_get(x_34, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_34, 1);
lean_inc(x_88);
x_89 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_90 = lean_ctor_get(x_35, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_35, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_35, 2);
lean_inc(x_92);
x_93 = lean_ctor_get_uint8(x_35, sizeof(void*)*3 + 8);
lean_dec(x_35);
x_94 = l_Lean_Expr_lam___override(x_90, x_91, x_92, x_93);
x_95 = l_Lean_Expr_forallE___override(x_87, x_88, x_94, x_89);
x_96 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_95, x_4, x_5, x_6, x_7, x_86);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_95);
return x_96;
}
case 7:
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_35, 2);
lean_inc(x_97);
switch (lean_obj_tag(x_97)) {
case 0:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_98 = lean_ctor_get(x_33, 1);
lean_inc(x_98);
lean_dec(x_33);
x_99 = lean_ctor_get(x_34, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_34, 1);
lean_inc(x_100);
x_101 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_102 = lean_ctor_get(x_35, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_35, 1);
lean_inc(x_103);
x_104 = lean_ctor_get_uint8(x_35, sizeof(void*)*3 + 8);
lean_dec(x_35);
x_105 = lean_ctor_get(x_97, 0);
lean_inc(x_105);
lean_dec(x_97);
x_106 = l_Lean_Expr_bvar___override(x_105);
x_107 = l_Lean_Expr_forallE___override(x_102, x_103, x_106, x_104);
x_108 = l_Lean_Expr_forallE___override(x_99, x_100, x_107, x_101);
x_109 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_108, x_4, x_5, x_6, x_7, x_98);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_108);
return x_109;
}
case 1:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_110 = lean_ctor_get(x_33, 1);
lean_inc(x_110);
lean_dec(x_33);
x_111 = lean_ctor_get(x_34, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_34, 1);
lean_inc(x_112);
x_113 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_114 = lean_ctor_get(x_35, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_35, 1);
lean_inc(x_115);
x_116 = lean_ctor_get_uint8(x_35, sizeof(void*)*3 + 8);
lean_dec(x_35);
x_117 = lean_ctor_get(x_97, 0);
lean_inc(x_117);
lean_dec(x_97);
x_118 = l_Lean_Expr_fvar___override(x_117);
x_119 = l_Lean_Expr_forallE___override(x_114, x_115, x_118, x_116);
x_120 = l_Lean_Expr_forallE___override(x_111, x_112, x_119, x_113);
x_121 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_120, x_4, x_5, x_6, x_7, x_110);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_120);
return x_121;
}
case 2:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_122 = lean_ctor_get(x_33, 1);
lean_inc(x_122);
lean_dec(x_33);
x_123 = lean_ctor_get(x_34, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_34, 1);
lean_inc(x_124);
x_125 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_126 = lean_ctor_get(x_35, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_35, 1);
lean_inc(x_127);
x_128 = lean_ctor_get_uint8(x_35, sizeof(void*)*3 + 8);
lean_dec(x_35);
x_129 = lean_ctor_get(x_97, 0);
lean_inc(x_129);
lean_dec(x_97);
x_130 = l_Lean_Expr_mvar___override(x_129);
x_131 = l_Lean_Expr_forallE___override(x_126, x_127, x_130, x_128);
x_132 = l_Lean_Expr_forallE___override(x_123, x_124, x_131, x_125);
x_133 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_132, x_4, x_5, x_6, x_7, x_122);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_132);
return x_133;
}
case 3:
{
uint8_t x_134; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_134 = !lean_is_exclusive(x_33);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_135 = lean_ctor_get(x_33, 0);
lean_dec(x_135);
x_136 = lean_ctor_get(x_97, 0);
lean_inc(x_136);
lean_dec(x_97);
x_137 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
x_138 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
x_139 = lean_mk_string_unchecked("rec", 3, 3);
x_140 = l_Lean_Name_mkStr2(x_9, x_139);
x_141 = lean_box(0);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_141);
lean_ctor_set(x_13, 0, x_31);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_136);
lean_ctor_set(x_142, 1, x_13);
x_143 = l_Lean_Expr_const___override(x_140, x_142);
x_144 = lean_unsigned_to_nat(6u);
x_145 = lean_mk_empty_array_with_capacity(x_144);
x_146 = lean_array_push(x_145, x_29);
x_147 = lean_array_push(x_146, x_137);
x_148 = lean_array_push(x_147, x_1);
x_149 = lean_array_push(x_148, x_2);
x_150 = lean_array_push(x_149, x_138);
x_151 = lean_array_push(x_150, x_3);
x_152 = l_Lean_mkAppN(x_143, x_151);
lean_dec(x_151);
lean_ctor_set(x_33, 0, x_152);
return x_33;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_153 = lean_ctor_get(x_33, 1);
lean_inc(x_153);
lean_dec(x_33);
x_154 = lean_ctor_get(x_97, 0);
lean_inc(x_154);
lean_dec(x_97);
x_155 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
x_156 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
x_157 = lean_mk_string_unchecked("rec", 3, 3);
x_158 = l_Lean_Name_mkStr2(x_9, x_157);
x_159 = lean_box(0);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_159);
lean_ctor_set(x_13, 0, x_31);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_154);
lean_ctor_set(x_160, 1, x_13);
x_161 = l_Lean_Expr_const___override(x_158, x_160);
x_162 = lean_unsigned_to_nat(6u);
x_163 = lean_mk_empty_array_with_capacity(x_162);
x_164 = lean_array_push(x_163, x_29);
x_165 = lean_array_push(x_164, x_155);
x_166 = lean_array_push(x_165, x_1);
x_167 = lean_array_push(x_166, x_2);
x_168 = lean_array_push(x_167, x_156);
x_169 = lean_array_push(x_168, x_3);
x_170 = l_Lean_mkAppN(x_161, x_169);
lean_dec(x_169);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_153);
return x_171;
}
}
case 4:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_172 = lean_ctor_get(x_33, 1);
lean_inc(x_172);
lean_dec(x_33);
x_173 = lean_ctor_get(x_34, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_34, 1);
lean_inc(x_174);
x_175 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_176 = lean_ctor_get(x_35, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_35, 1);
lean_inc(x_177);
x_178 = lean_ctor_get_uint8(x_35, sizeof(void*)*3 + 8);
lean_dec(x_35);
x_179 = lean_ctor_get(x_97, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_97, 1);
lean_inc(x_180);
lean_dec(x_97);
x_181 = l_Lean_Expr_const___override(x_179, x_180);
x_182 = l_Lean_Expr_forallE___override(x_176, x_177, x_181, x_178);
x_183 = l_Lean_Expr_forallE___override(x_173, x_174, x_182, x_175);
x_184 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_183, x_4, x_5, x_6, x_7, x_172);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_183);
return x_184;
}
case 5:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_185 = lean_ctor_get(x_33, 1);
lean_inc(x_185);
lean_dec(x_33);
x_186 = lean_ctor_get(x_34, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_34, 1);
lean_inc(x_187);
x_188 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_189 = lean_ctor_get(x_35, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_35, 1);
lean_inc(x_190);
x_191 = lean_ctor_get_uint8(x_35, sizeof(void*)*3 + 8);
lean_dec(x_35);
x_192 = lean_ctor_get(x_97, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_97, 1);
lean_inc(x_193);
lean_dec(x_97);
x_194 = l_Lean_Expr_app___override(x_192, x_193);
x_195 = l_Lean_Expr_forallE___override(x_189, x_190, x_194, x_191);
x_196 = l_Lean_Expr_forallE___override(x_186, x_187, x_195, x_188);
x_197 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_196, x_4, x_5, x_6, x_7, x_185);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_196);
return x_197;
}
case 6:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_198 = lean_ctor_get(x_33, 1);
lean_inc(x_198);
lean_dec(x_33);
x_199 = lean_ctor_get(x_34, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_34, 1);
lean_inc(x_200);
x_201 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_202 = lean_ctor_get(x_35, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_35, 1);
lean_inc(x_203);
x_204 = lean_ctor_get_uint8(x_35, sizeof(void*)*3 + 8);
lean_dec(x_35);
x_205 = lean_ctor_get(x_97, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_97, 1);
lean_inc(x_206);
x_207 = lean_ctor_get(x_97, 2);
lean_inc(x_207);
x_208 = lean_ctor_get_uint8(x_97, sizeof(void*)*3 + 8);
lean_dec(x_97);
x_209 = l_Lean_Expr_lam___override(x_205, x_206, x_207, x_208);
x_210 = l_Lean_Expr_forallE___override(x_202, x_203, x_209, x_204);
x_211 = l_Lean_Expr_forallE___override(x_199, x_200, x_210, x_201);
x_212 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_211, x_4, x_5, x_6, x_7, x_198);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_211);
return x_212;
}
case 7:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_213 = lean_ctor_get(x_33, 1);
lean_inc(x_213);
lean_dec(x_33);
x_214 = lean_ctor_get(x_34, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_34, 1);
lean_inc(x_215);
x_216 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_217 = lean_ctor_get(x_35, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_35, 1);
lean_inc(x_218);
x_219 = lean_ctor_get_uint8(x_35, sizeof(void*)*3 + 8);
lean_dec(x_35);
x_220 = lean_ctor_get(x_97, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_97, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_97, 2);
lean_inc(x_222);
x_223 = lean_ctor_get_uint8(x_97, sizeof(void*)*3 + 8);
lean_dec(x_97);
x_224 = l_Lean_Expr_forallE___override(x_220, x_221, x_222, x_223);
x_225 = l_Lean_Expr_forallE___override(x_217, x_218, x_224, x_219);
x_226 = l_Lean_Expr_forallE___override(x_214, x_215, x_225, x_216);
x_227 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_226, x_4, x_5, x_6, x_7, x_213);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_226);
return x_227;
}
case 8:
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_228 = lean_ctor_get(x_33, 1);
lean_inc(x_228);
lean_dec(x_33);
x_229 = lean_ctor_get(x_34, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_34, 1);
lean_inc(x_230);
x_231 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_232 = lean_ctor_get(x_35, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_35, 1);
lean_inc(x_233);
x_234 = lean_ctor_get_uint8(x_35, sizeof(void*)*3 + 8);
lean_dec(x_35);
x_235 = lean_ctor_get(x_97, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_97, 1);
lean_inc(x_236);
x_237 = lean_ctor_get(x_97, 2);
lean_inc(x_237);
x_238 = lean_ctor_get(x_97, 3);
lean_inc(x_238);
x_239 = lean_ctor_get_uint8(x_97, sizeof(void*)*4 + 8);
lean_dec(x_97);
x_240 = l_Lean_Expr_letE___override(x_235, x_236, x_237, x_238, x_239);
x_241 = l_Lean_Expr_forallE___override(x_232, x_233, x_240, x_234);
x_242 = l_Lean_Expr_forallE___override(x_229, x_230, x_241, x_231);
x_243 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_242, x_4, x_5, x_6, x_7, x_228);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_242);
return x_243;
}
case 9:
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_244 = lean_ctor_get(x_33, 1);
lean_inc(x_244);
lean_dec(x_33);
x_245 = lean_ctor_get(x_34, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_34, 1);
lean_inc(x_246);
x_247 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_248 = lean_ctor_get(x_35, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_35, 1);
lean_inc(x_249);
x_250 = lean_ctor_get_uint8(x_35, sizeof(void*)*3 + 8);
lean_dec(x_35);
x_251 = lean_ctor_get(x_97, 0);
lean_inc(x_251);
lean_dec(x_97);
x_252 = l_Lean_Expr_lit___override(x_251);
x_253 = l_Lean_Expr_forallE___override(x_248, x_249, x_252, x_250);
x_254 = l_Lean_Expr_forallE___override(x_245, x_246, x_253, x_247);
x_255 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_254, x_4, x_5, x_6, x_7, x_244);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_254);
return x_255;
}
case 10:
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_256 = lean_ctor_get(x_33, 1);
lean_inc(x_256);
lean_dec(x_33);
x_257 = lean_ctor_get(x_34, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_34, 1);
lean_inc(x_258);
x_259 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_260 = lean_ctor_get(x_35, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_35, 1);
lean_inc(x_261);
x_262 = lean_ctor_get_uint8(x_35, sizeof(void*)*3 + 8);
lean_dec(x_35);
x_263 = lean_ctor_get(x_97, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_97, 1);
lean_inc(x_264);
lean_dec(x_97);
x_265 = l_Lean_Expr_mdata___override(x_263, x_264);
x_266 = l_Lean_Expr_forallE___override(x_260, x_261, x_265, x_262);
x_267 = l_Lean_Expr_forallE___override(x_257, x_258, x_266, x_259);
x_268 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_267, x_4, x_5, x_6, x_7, x_256);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_267);
return x_268;
}
default: 
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_269 = lean_ctor_get(x_33, 1);
lean_inc(x_269);
lean_dec(x_33);
x_270 = lean_ctor_get(x_34, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_34, 1);
lean_inc(x_271);
x_272 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_273 = lean_ctor_get(x_35, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_35, 1);
lean_inc(x_274);
x_275 = lean_ctor_get_uint8(x_35, sizeof(void*)*3 + 8);
lean_dec(x_35);
x_276 = lean_ctor_get(x_97, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_97, 1);
lean_inc(x_277);
x_278 = lean_ctor_get(x_97, 2);
lean_inc(x_278);
lean_dec(x_97);
x_279 = l_Lean_Expr_proj___override(x_276, x_277, x_278);
x_280 = l_Lean_Expr_forallE___override(x_273, x_274, x_279, x_275);
x_281 = l_Lean_Expr_forallE___override(x_270, x_271, x_280, x_272);
x_282 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_281, x_4, x_5, x_6, x_7, x_269);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_281);
return x_282;
}
}
}
case 8:
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_283 = lean_ctor_get(x_33, 1);
lean_inc(x_283);
lean_dec(x_33);
x_284 = lean_ctor_get(x_34, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_34, 1);
lean_inc(x_285);
x_286 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_287 = lean_ctor_get(x_35, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_35, 1);
lean_inc(x_288);
x_289 = lean_ctor_get(x_35, 2);
lean_inc(x_289);
x_290 = lean_ctor_get(x_35, 3);
lean_inc(x_290);
x_291 = lean_ctor_get_uint8(x_35, sizeof(void*)*4 + 8);
lean_dec(x_35);
x_292 = l_Lean_Expr_letE___override(x_287, x_288, x_289, x_290, x_291);
x_293 = l_Lean_Expr_forallE___override(x_284, x_285, x_292, x_286);
x_294 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_293, x_4, x_5, x_6, x_7, x_283);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_293);
return x_294;
}
case 9:
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_295 = lean_ctor_get(x_33, 1);
lean_inc(x_295);
lean_dec(x_33);
x_296 = lean_ctor_get(x_34, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_34, 1);
lean_inc(x_297);
x_298 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_299 = lean_ctor_get(x_35, 0);
lean_inc(x_299);
lean_dec(x_35);
x_300 = l_Lean_Expr_lit___override(x_299);
x_301 = l_Lean_Expr_forallE___override(x_296, x_297, x_300, x_298);
x_302 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_301, x_4, x_5, x_6, x_7, x_295);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_301);
return x_302;
}
case 10:
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_303 = lean_ctor_get(x_33, 1);
lean_inc(x_303);
lean_dec(x_33);
x_304 = lean_ctor_get(x_34, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_34, 1);
lean_inc(x_305);
x_306 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_307 = lean_ctor_get(x_35, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_35, 1);
lean_inc(x_308);
lean_dec(x_35);
x_309 = l_Lean_Expr_mdata___override(x_307, x_308);
x_310 = l_Lean_Expr_forallE___override(x_304, x_305, x_309, x_306);
x_311 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_310, x_4, x_5, x_6, x_7, x_303);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_310);
return x_311;
}
default: 
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_312 = lean_ctor_get(x_33, 1);
lean_inc(x_312);
lean_dec(x_33);
x_313 = lean_ctor_get(x_34, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_34, 1);
lean_inc(x_314);
x_315 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_316 = lean_ctor_get(x_35, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_35, 1);
lean_inc(x_317);
x_318 = lean_ctor_get(x_35, 2);
lean_inc(x_318);
lean_dec(x_35);
x_319 = l_Lean_Expr_proj___override(x_316, x_317, x_318);
x_320 = l_Lean_Expr_forallE___override(x_313, x_314, x_319, x_315);
x_321 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_320, x_4, x_5, x_6, x_7, x_312);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_320);
return x_321;
}
}
}
else
{
lean_object* x_322; lean_object* x_323; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_322 = lean_ctor_get(x_33, 1);
lean_inc(x_322);
lean_dec(x_33);
x_323 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_34, x_4, x_5, x_6, x_7, x_322);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_34);
return x_323;
}
}
else
{
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_33;
}
}
else
{
uint8_t x_324; 
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_324 = !lean_is_exclusive(x_30);
if (x_324 == 0)
{
return x_30;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_30, 0);
x_326 = lean_ctor_get(x_30, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_30);
x_327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
return x_327;
}
}
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; 
x_328 = lean_ctor_get(x_13, 0);
x_329 = lean_ctor_get(x_13, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_13);
lean_inc(x_9);
x_330 = l_Lean_Name_mkStr1(x_9);
x_331 = lean_unsigned_to_nat(3u);
x_332 = l_Lean_Expr_isAppOfArity(x_328, x_330, x_331);
lean_dec(x_330);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_328);
lean_dec(x_2);
lean_dec(x_1);
x_333 = lean_mk_string_unchecked("rec", 3, 3);
x_334 = l_Lean_Name_mkStr2(x_9, x_333);
x_335 = lean_mk_string_unchecked("equality proof expected", 23, 23);
x_336 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_336, 0, x_335);
x_337 = l_Lean_MessageData_ofFormat(x_336);
x_338 = l_Lean_indentExpr(x_3);
x_339 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
x_340 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_334, x_339, x_4, x_5, x_6, x_7, x_329);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_340;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_341 = l_Lean_Expr_appFn_x21(x_328);
x_342 = l_Lean_Expr_appFn_x21(x_341);
x_343 = l_Lean_Expr_appArg_x21(x_342);
lean_dec(x_342);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_343);
x_344 = l_Lean_Meta_getLevel(x_343, x_4, x_5, x_6, x_7, x_329);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
lean_dec(x_344);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_347 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_4, x_5, x_6, x_7, x_346);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; 
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
if (lean_obj_tag(x_348) == 7)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_348, 2);
lean_inc(x_349);
switch (lean_obj_tag(x_349)) {
case 0:
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_350 = lean_ctor_get(x_347, 1);
lean_inc(x_350);
lean_dec(x_347);
x_351 = lean_ctor_get(x_348, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_348, 1);
lean_inc(x_352);
x_353 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_354 = lean_ctor_get(x_349, 0);
lean_inc(x_354);
lean_dec(x_349);
x_355 = l_Lean_Expr_bvar___override(x_354);
x_356 = l_Lean_Expr_forallE___override(x_351, x_352, x_355, x_353);
x_357 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_356, x_4, x_5, x_6, x_7, x_350);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_356);
return x_357;
}
case 1:
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; uint8_t x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_358 = lean_ctor_get(x_347, 1);
lean_inc(x_358);
lean_dec(x_347);
x_359 = lean_ctor_get(x_348, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_348, 1);
lean_inc(x_360);
x_361 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_362 = lean_ctor_get(x_349, 0);
lean_inc(x_362);
lean_dec(x_349);
x_363 = l_Lean_Expr_fvar___override(x_362);
x_364 = l_Lean_Expr_forallE___override(x_359, x_360, x_363, x_361);
x_365 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_364, x_4, x_5, x_6, x_7, x_358);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_364);
return x_365;
}
case 2:
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_366 = lean_ctor_get(x_347, 1);
lean_inc(x_366);
lean_dec(x_347);
x_367 = lean_ctor_get(x_348, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_348, 1);
lean_inc(x_368);
x_369 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_370 = lean_ctor_get(x_349, 0);
lean_inc(x_370);
lean_dec(x_349);
x_371 = l_Lean_Expr_mvar___override(x_370);
x_372 = l_Lean_Expr_forallE___override(x_367, x_368, x_371, x_369);
x_373 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_372, x_4, x_5, x_6, x_7, x_366);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_372);
return x_373;
}
case 3:
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_374 = lean_ctor_get(x_347, 1);
lean_inc(x_374);
lean_dec(x_347);
x_375 = lean_ctor_get(x_348, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_348, 1);
lean_inc(x_376);
x_377 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_378 = lean_ctor_get(x_349, 0);
lean_inc(x_378);
lean_dec(x_349);
x_379 = l_Lean_Expr_sort___override(x_378);
x_380 = l_Lean_Expr_forallE___override(x_375, x_376, x_379, x_377);
x_381 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_380, x_4, x_5, x_6, x_7, x_374);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_380);
return x_381;
}
case 4:
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_382 = lean_ctor_get(x_347, 1);
lean_inc(x_382);
lean_dec(x_347);
x_383 = lean_ctor_get(x_348, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_348, 1);
lean_inc(x_384);
x_385 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_386 = lean_ctor_get(x_349, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_349, 1);
lean_inc(x_387);
lean_dec(x_349);
x_388 = l_Lean_Expr_const___override(x_386, x_387);
x_389 = l_Lean_Expr_forallE___override(x_383, x_384, x_388, x_385);
x_390 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_389, x_4, x_5, x_6, x_7, x_382);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_389);
return x_390;
}
case 5:
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_391 = lean_ctor_get(x_347, 1);
lean_inc(x_391);
lean_dec(x_347);
x_392 = lean_ctor_get(x_348, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_348, 1);
lean_inc(x_393);
x_394 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_395 = lean_ctor_get(x_349, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_349, 1);
lean_inc(x_396);
lean_dec(x_349);
x_397 = l_Lean_Expr_app___override(x_395, x_396);
x_398 = l_Lean_Expr_forallE___override(x_392, x_393, x_397, x_394);
x_399 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_398, x_4, x_5, x_6, x_7, x_391);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_398);
return x_399;
}
case 6:
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_400 = lean_ctor_get(x_347, 1);
lean_inc(x_400);
lean_dec(x_347);
x_401 = lean_ctor_get(x_348, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_348, 1);
lean_inc(x_402);
x_403 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_404 = lean_ctor_get(x_349, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_349, 1);
lean_inc(x_405);
x_406 = lean_ctor_get(x_349, 2);
lean_inc(x_406);
x_407 = lean_ctor_get_uint8(x_349, sizeof(void*)*3 + 8);
lean_dec(x_349);
x_408 = l_Lean_Expr_lam___override(x_404, x_405, x_406, x_407);
x_409 = l_Lean_Expr_forallE___override(x_401, x_402, x_408, x_403);
x_410 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_409, x_4, x_5, x_6, x_7, x_400);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_409);
return x_410;
}
case 7:
{
lean_object* x_411; 
x_411 = lean_ctor_get(x_349, 2);
lean_inc(x_411);
switch (lean_obj_tag(x_411)) {
case 0:
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_412 = lean_ctor_get(x_347, 1);
lean_inc(x_412);
lean_dec(x_347);
x_413 = lean_ctor_get(x_348, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_348, 1);
lean_inc(x_414);
x_415 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_416 = lean_ctor_get(x_349, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_349, 1);
lean_inc(x_417);
x_418 = lean_ctor_get_uint8(x_349, sizeof(void*)*3 + 8);
lean_dec(x_349);
x_419 = lean_ctor_get(x_411, 0);
lean_inc(x_419);
lean_dec(x_411);
x_420 = l_Lean_Expr_bvar___override(x_419);
x_421 = l_Lean_Expr_forallE___override(x_416, x_417, x_420, x_418);
x_422 = l_Lean_Expr_forallE___override(x_413, x_414, x_421, x_415);
x_423 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_422, x_4, x_5, x_6, x_7, x_412);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_422);
return x_423;
}
case 1:
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; lean_object* x_429; uint8_t x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_424 = lean_ctor_get(x_347, 1);
lean_inc(x_424);
lean_dec(x_347);
x_425 = lean_ctor_get(x_348, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_348, 1);
lean_inc(x_426);
x_427 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_428 = lean_ctor_get(x_349, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_349, 1);
lean_inc(x_429);
x_430 = lean_ctor_get_uint8(x_349, sizeof(void*)*3 + 8);
lean_dec(x_349);
x_431 = lean_ctor_get(x_411, 0);
lean_inc(x_431);
lean_dec(x_411);
x_432 = l_Lean_Expr_fvar___override(x_431);
x_433 = l_Lean_Expr_forallE___override(x_428, x_429, x_432, x_430);
x_434 = l_Lean_Expr_forallE___override(x_425, x_426, x_433, x_427);
x_435 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_434, x_4, x_5, x_6, x_7, x_424);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_434);
return x_435;
}
case 2:
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_436 = lean_ctor_get(x_347, 1);
lean_inc(x_436);
lean_dec(x_347);
x_437 = lean_ctor_get(x_348, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_348, 1);
lean_inc(x_438);
x_439 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_440 = lean_ctor_get(x_349, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_349, 1);
lean_inc(x_441);
x_442 = lean_ctor_get_uint8(x_349, sizeof(void*)*3 + 8);
lean_dec(x_349);
x_443 = lean_ctor_get(x_411, 0);
lean_inc(x_443);
lean_dec(x_411);
x_444 = l_Lean_Expr_mvar___override(x_443);
x_445 = l_Lean_Expr_forallE___override(x_440, x_441, x_444, x_442);
x_446 = l_Lean_Expr_forallE___override(x_437, x_438, x_445, x_439);
x_447 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_446, x_4, x_5, x_6, x_7, x_436);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_446);
return x_447;
}
case 3:
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_448 = lean_ctor_get(x_347, 1);
lean_inc(x_448);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_449 = x_347;
} else {
 lean_dec_ref(x_347);
 x_449 = lean_box(0);
}
x_450 = lean_ctor_get(x_411, 0);
lean_inc(x_450);
lean_dec(x_411);
x_451 = l_Lean_Expr_appArg_x21(x_341);
lean_dec(x_341);
x_452 = l_Lean_Expr_appArg_x21(x_328);
lean_dec(x_328);
x_453 = lean_mk_string_unchecked("rec", 3, 3);
x_454 = l_Lean_Name_mkStr2(x_9, x_453);
x_455 = lean_box(0);
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_345);
lean_ctor_set(x_456, 1, x_455);
x_457 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_457, 0, x_450);
lean_ctor_set(x_457, 1, x_456);
x_458 = l_Lean_Expr_const___override(x_454, x_457);
x_459 = lean_unsigned_to_nat(6u);
x_460 = lean_mk_empty_array_with_capacity(x_459);
x_461 = lean_array_push(x_460, x_343);
x_462 = lean_array_push(x_461, x_451);
x_463 = lean_array_push(x_462, x_1);
x_464 = lean_array_push(x_463, x_2);
x_465 = lean_array_push(x_464, x_452);
x_466 = lean_array_push(x_465, x_3);
x_467 = l_Lean_mkAppN(x_458, x_466);
lean_dec(x_466);
if (lean_is_scalar(x_449)) {
 x_468 = lean_alloc_ctor(0, 2, 0);
} else {
 x_468 = x_449;
}
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set(x_468, 1, x_448);
return x_468;
}
case 4:
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; uint8_t x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_469 = lean_ctor_get(x_347, 1);
lean_inc(x_469);
lean_dec(x_347);
x_470 = lean_ctor_get(x_348, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_348, 1);
lean_inc(x_471);
x_472 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_473 = lean_ctor_get(x_349, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_349, 1);
lean_inc(x_474);
x_475 = lean_ctor_get_uint8(x_349, sizeof(void*)*3 + 8);
lean_dec(x_349);
x_476 = lean_ctor_get(x_411, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_411, 1);
lean_inc(x_477);
lean_dec(x_411);
x_478 = l_Lean_Expr_const___override(x_476, x_477);
x_479 = l_Lean_Expr_forallE___override(x_473, x_474, x_478, x_475);
x_480 = l_Lean_Expr_forallE___override(x_470, x_471, x_479, x_472);
x_481 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_480, x_4, x_5, x_6, x_7, x_469);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_480);
return x_481;
}
case 5:
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_482 = lean_ctor_get(x_347, 1);
lean_inc(x_482);
lean_dec(x_347);
x_483 = lean_ctor_get(x_348, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_348, 1);
lean_inc(x_484);
x_485 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_486 = lean_ctor_get(x_349, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_349, 1);
lean_inc(x_487);
x_488 = lean_ctor_get_uint8(x_349, sizeof(void*)*3 + 8);
lean_dec(x_349);
x_489 = lean_ctor_get(x_411, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_411, 1);
lean_inc(x_490);
lean_dec(x_411);
x_491 = l_Lean_Expr_app___override(x_489, x_490);
x_492 = l_Lean_Expr_forallE___override(x_486, x_487, x_491, x_488);
x_493 = l_Lean_Expr_forallE___override(x_483, x_484, x_492, x_485);
x_494 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_493, x_4, x_5, x_6, x_7, x_482);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_493);
return x_494;
}
case 6:
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; uint8_t x_498; lean_object* x_499; lean_object* x_500; uint8_t x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; uint8_t x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_495 = lean_ctor_get(x_347, 1);
lean_inc(x_495);
lean_dec(x_347);
x_496 = lean_ctor_get(x_348, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_348, 1);
lean_inc(x_497);
x_498 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_499 = lean_ctor_get(x_349, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_349, 1);
lean_inc(x_500);
x_501 = lean_ctor_get_uint8(x_349, sizeof(void*)*3 + 8);
lean_dec(x_349);
x_502 = lean_ctor_get(x_411, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_411, 1);
lean_inc(x_503);
x_504 = lean_ctor_get(x_411, 2);
lean_inc(x_504);
x_505 = lean_ctor_get_uint8(x_411, sizeof(void*)*3 + 8);
lean_dec(x_411);
x_506 = l_Lean_Expr_lam___override(x_502, x_503, x_504, x_505);
x_507 = l_Lean_Expr_forallE___override(x_499, x_500, x_506, x_501);
x_508 = l_Lean_Expr_forallE___override(x_496, x_497, x_507, x_498);
x_509 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_508, x_4, x_5, x_6, x_7, x_495);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_508);
return x_509;
}
case 7:
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; uint8_t x_513; lean_object* x_514; lean_object* x_515; uint8_t x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; uint8_t x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_510 = lean_ctor_get(x_347, 1);
lean_inc(x_510);
lean_dec(x_347);
x_511 = lean_ctor_get(x_348, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_348, 1);
lean_inc(x_512);
x_513 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_514 = lean_ctor_get(x_349, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_349, 1);
lean_inc(x_515);
x_516 = lean_ctor_get_uint8(x_349, sizeof(void*)*3 + 8);
lean_dec(x_349);
x_517 = lean_ctor_get(x_411, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_411, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_411, 2);
lean_inc(x_519);
x_520 = lean_ctor_get_uint8(x_411, sizeof(void*)*3 + 8);
lean_dec(x_411);
x_521 = l_Lean_Expr_forallE___override(x_517, x_518, x_519, x_520);
x_522 = l_Lean_Expr_forallE___override(x_514, x_515, x_521, x_516);
x_523 = l_Lean_Expr_forallE___override(x_511, x_512, x_522, x_513);
x_524 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_523, x_4, x_5, x_6, x_7, x_510);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_523);
return x_524;
}
case 8:
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; uint8_t x_528; lean_object* x_529; lean_object* x_530; uint8_t x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; uint8_t x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_525 = lean_ctor_get(x_347, 1);
lean_inc(x_525);
lean_dec(x_347);
x_526 = lean_ctor_get(x_348, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_348, 1);
lean_inc(x_527);
x_528 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_529 = lean_ctor_get(x_349, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_349, 1);
lean_inc(x_530);
x_531 = lean_ctor_get_uint8(x_349, sizeof(void*)*3 + 8);
lean_dec(x_349);
x_532 = lean_ctor_get(x_411, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_411, 1);
lean_inc(x_533);
x_534 = lean_ctor_get(x_411, 2);
lean_inc(x_534);
x_535 = lean_ctor_get(x_411, 3);
lean_inc(x_535);
x_536 = lean_ctor_get_uint8(x_411, sizeof(void*)*4 + 8);
lean_dec(x_411);
x_537 = l_Lean_Expr_letE___override(x_532, x_533, x_534, x_535, x_536);
x_538 = l_Lean_Expr_forallE___override(x_529, x_530, x_537, x_531);
x_539 = l_Lean_Expr_forallE___override(x_526, x_527, x_538, x_528);
x_540 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_539, x_4, x_5, x_6, x_7, x_525);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_539);
return x_540;
}
case 9:
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; uint8_t x_544; lean_object* x_545; lean_object* x_546; uint8_t x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_541 = lean_ctor_get(x_347, 1);
lean_inc(x_541);
lean_dec(x_347);
x_542 = lean_ctor_get(x_348, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_348, 1);
lean_inc(x_543);
x_544 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_545 = lean_ctor_get(x_349, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_349, 1);
lean_inc(x_546);
x_547 = lean_ctor_get_uint8(x_349, sizeof(void*)*3 + 8);
lean_dec(x_349);
x_548 = lean_ctor_get(x_411, 0);
lean_inc(x_548);
lean_dec(x_411);
x_549 = l_Lean_Expr_lit___override(x_548);
x_550 = l_Lean_Expr_forallE___override(x_545, x_546, x_549, x_547);
x_551 = l_Lean_Expr_forallE___override(x_542, x_543, x_550, x_544);
x_552 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_551, x_4, x_5, x_6, x_7, x_541);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_551);
return x_552;
}
case 10:
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; uint8_t x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_553 = lean_ctor_get(x_347, 1);
lean_inc(x_553);
lean_dec(x_347);
x_554 = lean_ctor_get(x_348, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_348, 1);
lean_inc(x_555);
x_556 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_557 = lean_ctor_get(x_349, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_349, 1);
lean_inc(x_558);
x_559 = lean_ctor_get_uint8(x_349, sizeof(void*)*3 + 8);
lean_dec(x_349);
x_560 = lean_ctor_get(x_411, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_411, 1);
lean_inc(x_561);
lean_dec(x_411);
x_562 = l_Lean_Expr_mdata___override(x_560, x_561);
x_563 = l_Lean_Expr_forallE___override(x_557, x_558, x_562, x_559);
x_564 = l_Lean_Expr_forallE___override(x_554, x_555, x_563, x_556);
x_565 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_564, x_4, x_5, x_6, x_7, x_553);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_564);
return x_565;
}
default: 
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; uint8_t x_569; lean_object* x_570; lean_object* x_571; uint8_t x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_566 = lean_ctor_get(x_347, 1);
lean_inc(x_566);
lean_dec(x_347);
x_567 = lean_ctor_get(x_348, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_348, 1);
lean_inc(x_568);
x_569 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_570 = lean_ctor_get(x_349, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_349, 1);
lean_inc(x_571);
x_572 = lean_ctor_get_uint8(x_349, sizeof(void*)*3 + 8);
lean_dec(x_349);
x_573 = lean_ctor_get(x_411, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_411, 1);
lean_inc(x_574);
x_575 = lean_ctor_get(x_411, 2);
lean_inc(x_575);
lean_dec(x_411);
x_576 = l_Lean_Expr_proj___override(x_573, x_574, x_575);
x_577 = l_Lean_Expr_forallE___override(x_570, x_571, x_576, x_572);
x_578 = l_Lean_Expr_forallE___override(x_567, x_568, x_577, x_569);
x_579 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_578, x_4, x_5, x_6, x_7, x_566);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_578);
return x_579;
}
}
}
case 8:
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; uint8_t x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; uint8_t x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_580 = lean_ctor_get(x_347, 1);
lean_inc(x_580);
lean_dec(x_347);
x_581 = lean_ctor_get(x_348, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_348, 1);
lean_inc(x_582);
x_583 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_584 = lean_ctor_get(x_349, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_349, 1);
lean_inc(x_585);
x_586 = lean_ctor_get(x_349, 2);
lean_inc(x_586);
x_587 = lean_ctor_get(x_349, 3);
lean_inc(x_587);
x_588 = lean_ctor_get_uint8(x_349, sizeof(void*)*4 + 8);
lean_dec(x_349);
x_589 = l_Lean_Expr_letE___override(x_584, x_585, x_586, x_587, x_588);
x_590 = l_Lean_Expr_forallE___override(x_581, x_582, x_589, x_583);
x_591 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_590, x_4, x_5, x_6, x_7, x_580);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_590);
return x_591;
}
case 9:
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; uint8_t x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_592 = lean_ctor_get(x_347, 1);
lean_inc(x_592);
lean_dec(x_347);
x_593 = lean_ctor_get(x_348, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_348, 1);
lean_inc(x_594);
x_595 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_596 = lean_ctor_get(x_349, 0);
lean_inc(x_596);
lean_dec(x_349);
x_597 = l_Lean_Expr_lit___override(x_596);
x_598 = l_Lean_Expr_forallE___override(x_593, x_594, x_597, x_595);
x_599 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_598, x_4, x_5, x_6, x_7, x_592);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_598);
return x_599;
}
case 10:
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; uint8_t x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_600 = lean_ctor_get(x_347, 1);
lean_inc(x_600);
lean_dec(x_347);
x_601 = lean_ctor_get(x_348, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_348, 1);
lean_inc(x_602);
x_603 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_604 = lean_ctor_get(x_349, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_349, 1);
lean_inc(x_605);
lean_dec(x_349);
x_606 = l_Lean_Expr_mdata___override(x_604, x_605);
x_607 = l_Lean_Expr_forallE___override(x_601, x_602, x_606, x_603);
x_608 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_607, x_4, x_5, x_6, x_7, x_600);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_607);
return x_608;
}
default: 
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; uint8_t x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_609 = lean_ctor_get(x_347, 1);
lean_inc(x_609);
lean_dec(x_347);
x_610 = lean_ctor_get(x_348, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_348, 1);
lean_inc(x_611);
x_612 = lean_ctor_get_uint8(x_348, sizeof(void*)*3 + 8);
lean_dec(x_348);
x_613 = lean_ctor_get(x_349, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_349, 1);
lean_inc(x_614);
x_615 = lean_ctor_get(x_349, 2);
lean_inc(x_615);
lean_dec(x_349);
x_616 = l_Lean_Expr_proj___override(x_613, x_614, x_615);
x_617 = l_Lean_Expr_forallE___override(x_610, x_611, x_616, x_612);
x_618 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_617, x_4, x_5, x_6, x_7, x_609);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_617);
return x_618;
}
}
}
else
{
lean_object* x_619; lean_object* x_620; 
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_3);
lean_dec(x_2);
x_619 = lean_ctor_get(x_347, 1);
lean_inc(x_619);
lean_dec(x_347);
x_620 = l_Lean_Meta_mkEqRec___lam__0(x_9, x_1, x_348, x_4, x_5, x_6, x_7, x_619);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_348);
return x_620;
}
}
else
{
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_347;
}
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_328);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_621 = lean_ctor_get(x_344, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_344, 1);
lean_inc(x_622);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_623 = x_344;
} else {
 lean_dec_ref(x_344);
 x_623 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_624 = lean_alloc_ctor(1, 2, 0);
} else {
 x_624 = x_623;
}
lean_ctor_set(x_624, 0, x_621);
lean_ctor_set(x_624, 1, x_622);
return x_624;
}
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
else
{
lean_object* x_625; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_625 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_625, 0, x_2);
lean_ctor_set(x_625, 1, x_8);
return x_625;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkEqRec___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_mk_string_unchecked("Eq", 2, 2);
x_9 = lean_mk_string_unchecked("mp", 2, 2);
x_10 = l_Lean_Name_mkStr2(x_8, x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_mk_empty_array_with_capacity(x_11);
x_13 = lean_array_push(x_12, x_1);
x_14 = lean_array_push(x_13, x_2);
x_15 = l_Lean_Meta_mkAppM(x_10, x_14, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_mk_string_unchecked("Eq", 2, 2);
x_9 = lean_mk_string_unchecked("mpr", 3, 3);
x_10 = l_Lean_Name_mkStr2(x_8, x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_mk_empty_array_with_capacity(x_11);
x_13 = lean_array_push(x_12, x_1);
x_14 = lean_array_push(x_13, x_2);
x_15 = l_Lean_Meta_mkAppM(x_10, x_14, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_mk_string_unchecked("noConfusion", 11, 11);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("inductive type expected", 23, 23);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_MessageData_ofFormat(x_11);
x_13 = l_Lean_indentExpr(x_1);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_9, x_14, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_whnf(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_mk_string_unchecked("Eq", 2, 2);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Expr_isAppOfArity(x_13, x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_19 = lean_mk_string_unchecked("noConfusion", 11, 11);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_mk_string_unchecked("equality expected", 17, 17);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_MessageData_ofFormat(x_22);
x_24 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_13);
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_24);
lean_ctor_set(x_11, 0, x_23);
x_25 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_20, x_11, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_11);
x_26 = l_Lean_Expr_appFn_x21(x_13);
x_27 = l_Lean_Expr_appFn_x21(x_26);
x_28 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_29 = l_Lean_Meta_whnfD(x_28, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Expr_getAppFn(x_30);
if (lean_obj_tag(x_32) == 4)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_6, x_31);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_box(0);
x_41 = lean_unbox(x_40);
x_42 = l_Lean_Environment_find_x3f(x_39, x_33, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_free_object(x_35);
lean_dec(x_34);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_box(0);
x_44 = l_Lean_Meta_mkNoConfusion___lam__0(x_30, x_43, x_3, x_4, x_5, x_6, x_38);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_44;
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
lean_dec(x_42);
if (lean_obj_tag(x_45) == 5)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
lean_inc(x_1);
x_47 = l_Lean_Meta_getLevel(x_1, x_3, x_4, x_5, x_6, x_38);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = l_Lean_Expr_appArg_x21(x_26);
lean_dec(x_26);
x_51 = l_Lean_Expr_appArg_x21(x_13);
lean_dec(x_13);
x_52 = lean_ctor_get(x_46, 0);
lean_inc(x_52);
lean_dec(x_46);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_mk_string_unchecked("noConfusion", 11, 11);
x_55 = l_Lean_Name_str___override(x_53, x_54);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 0, x_49);
x_56 = l_Lean_Expr_const___override(x_55, x_35);
x_57 = lean_box(0);
x_58 = l_Lean_Expr_sort___override(x_57);
x_59 = l_Lean_Expr_getAppNumArgs(x_30);
lean_inc(x_59);
x_60 = lean_mk_array(x_59, x_58);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_sub(x_59, x_61);
lean_dec(x_59);
x_63 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_30, x_60, x_62);
x_64 = lean_unsigned_to_nat(4u);
x_65 = lean_mk_empty_array_with_capacity(x_64);
x_66 = lean_array_push(x_65, x_1);
x_67 = lean_array_push(x_66, x_50);
x_68 = lean_array_push(x_67, x_51);
x_69 = lean_array_push(x_68, x_2);
x_70 = l_Array_append(lean_box(0), x_63, x_69);
lean_dec(x_69);
x_71 = l_Lean_mkAppN(x_56, x_70);
lean_dec(x_70);
lean_ctor_set(x_47, 0, x_71);
return x_47;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_72 = lean_ctor_get(x_47, 0);
x_73 = lean_ctor_get(x_47, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_47);
x_74 = l_Lean_Expr_appArg_x21(x_26);
lean_dec(x_26);
x_75 = l_Lean_Expr_appArg_x21(x_13);
lean_dec(x_13);
x_76 = lean_ctor_get(x_46, 0);
lean_inc(x_76);
lean_dec(x_46);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_mk_string_unchecked("noConfusion", 11, 11);
x_79 = l_Lean_Name_str___override(x_77, x_78);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 0, x_72);
x_80 = l_Lean_Expr_const___override(x_79, x_35);
x_81 = lean_box(0);
x_82 = l_Lean_Expr_sort___override(x_81);
x_83 = l_Lean_Expr_getAppNumArgs(x_30);
lean_inc(x_83);
x_84 = lean_mk_array(x_83, x_82);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_sub(x_83, x_85);
lean_dec(x_83);
x_87 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_30, x_84, x_86);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_mk_empty_array_with_capacity(x_88);
x_90 = lean_array_push(x_89, x_1);
x_91 = lean_array_push(x_90, x_74);
x_92 = lean_array_push(x_91, x_75);
x_93 = lean_array_push(x_92, x_2);
x_94 = l_Array_append(lean_box(0), x_87, x_93);
lean_dec(x_93);
x_95 = l_Lean_mkAppN(x_80, x_94);
lean_dec(x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_73);
return x_96;
}
}
else
{
uint8_t x_97; 
lean_dec(x_46);
lean_free_object(x_35);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_47);
if (x_97 == 0)
{
return x_47;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_47, 0);
x_99 = lean_ctor_get(x_47, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_47);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_45);
lean_free_object(x_35);
lean_dec(x_34);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_101 = lean_box(0);
x_102 = l_Lean_Meta_mkNoConfusion___lam__0(x_30, x_101, x_3, x_4, x_5, x_6, x_38);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_35, 0);
x_104 = lean_ctor_get(x_35, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_35);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_box(0);
x_107 = lean_unbox(x_106);
x_108 = l_Lean_Environment_find_x3f(x_105, x_33, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_34);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_109 = lean_box(0);
x_110 = l_Lean_Meta_mkNoConfusion___lam__0(x_30, x_109, x_3, x_4, x_5, x_6, x_104);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_110;
}
else
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_108, 0);
lean_inc(x_111);
lean_dec(x_108);
if (lean_obj_tag(x_111) == 5)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec(x_111);
lean_inc(x_1);
x_113 = l_Lean_Meta_getLevel(x_1, x_3, x_4, x_5, x_6, x_104);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
x_117 = l_Lean_Expr_appArg_x21(x_26);
lean_dec(x_26);
x_118 = l_Lean_Expr_appArg_x21(x_13);
lean_dec(x_13);
x_119 = lean_ctor_get(x_112, 0);
lean_inc(x_119);
lean_dec(x_112);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_mk_string_unchecked("noConfusion", 11, 11);
x_122 = l_Lean_Name_str___override(x_120, x_121);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_114);
lean_ctor_set(x_123, 1, x_34);
x_124 = l_Lean_Expr_const___override(x_122, x_123);
x_125 = lean_box(0);
x_126 = l_Lean_Expr_sort___override(x_125);
x_127 = l_Lean_Expr_getAppNumArgs(x_30);
lean_inc(x_127);
x_128 = lean_mk_array(x_127, x_126);
x_129 = lean_unsigned_to_nat(1u);
x_130 = lean_nat_sub(x_127, x_129);
lean_dec(x_127);
x_131 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_30, x_128, x_130);
x_132 = lean_unsigned_to_nat(4u);
x_133 = lean_mk_empty_array_with_capacity(x_132);
x_134 = lean_array_push(x_133, x_1);
x_135 = lean_array_push(x_134, x_117);
x_136 = lean_array_push(x_135, x_118);
x_137 = lean_array_push(x_136, x_2);
x_138 = l_Array_append(lean_box(0), x_131, x_137);
lean_dec(x_137);
x_139 = l_Lean_mkAppN(x_124, x_138);
lean_dec(x_138);
if (lean_is_scalar(x_116)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_116;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_115);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_112);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_141 = lean_ctor_get(x_113, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_113, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_143 = x_113;
} else {
 lean_dec_ref(x_113);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_111);
lean_dec(x_34);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_145 = lean_box(0);
x_146 = l_Lean_Meta_mkNoConfusion___lam__0(x_30, x_145, x_3, x_4, x_5, x_6, x_104);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_146;
}
}
}
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_32);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_147 = lean_box(0);
x_148 = l_Lean_Meta_mkNoConfusion___lam__0(x_30, x_147, x_3, x_4, x_5, x_6, x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_148;
}
}
else
{
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_29;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_149 = lean_ctor_get(x_11, 0);
x_150 = lean_ctor_get(x_11, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_11);
x_151 = lean_mk_string_unchecked("Eq", 2, 2);
x_152 = l_Lean_Name_mkStr1(x_151);
x_153 = lean_unsigned_to_nat(3u);
x_154 = l_Lean_Expr_isAppOfArity(x_149, x_152, x_153);
lean_dec(x_152);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_1);
x_155 = lean_mk_string_unchecked("noConfusion", 11, 11);
x_156 = l_Lean_Name_mkStr1(x_155);
x_157 = lean_mk_string_unchecked("equality expected", 17, 17);
x_158 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = l_Lean_MessageData_ofFormat(x_158);
x_160 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_149);
x_161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_162 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_156, x_161, x_3, x_4, x_5, x_6, x_150);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = l_Lean_Expr_appFn_x21(x_149);
x_164 = l_Lean_Expr_appFn_x21(x_163);
x_165 = l_Lean_Expr_appArg_x21(x_164);
lean_dec(x_164);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_166 = l_Lean_Meta_whnfD(x_165, x_3, x_4, x_5, x_6, x_150);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = l_Lean_Expr_getAppFn(x_167);
if (lean_obj_tag(x_169) == 4)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_st_ref_get(x_6, x_168);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_175 = x_172;
} else {
 lean_dec_ref(x_172);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_173, 0);
lean_inc(x_176);
lean_dec(x_173);
x_177 = lean_box(0);
x_178 = lean_unbox(x_177);
x_179 = l_Lean_Environment_find_x3f(x_176, x_170, x_178);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_163);
lean_dec(x_149);
lean_dec(x_2);
lean_dec(x_1);
x_180 = lean_box(0);
x_181 = l_Lean_Meta_mkNoConfusion___lam__0(x_167, x_180, x_3, x_4, x_5, x_6, x_174);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_181;
}
else
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_179, 0);
lean_inc(x_182);
lean_dec(x_179);
if (lean_obj_tag(x_182) == 5)
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
lean_dec(x_182);
lean_inc(x_1);
x_184 = l_Lean_Meta_getLevel(x_1, x_3, x_4, x_5, x_6, x_174);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_187 = x_184;
} else {
 lean_dec_ref(x_184);
 x_187 = lean_box(0);
}
x_188 = l_Lean_Expr_appArg_x21(x_163);
lean_dec(x_163);
x_189 = l_Lean_Expr_appArg_x21(x_149);
lean_dec(x_149);
x_190 = lean_ctor_get(x_183, 0);
lean_inc(x_190);
lean_dec(x_183);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec(x_190);
x_192 = lean_mk_string_unchecked("noConfusion", 11, 11);
x_193 = l_Lean_Name_str___override(x_191, x_192);
if (lean_is_scalar(x_175)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_175;
 lean_ctor_set_tag(x_194, 1);
}
lean_ctor_set(x_194, 0, x_185);
lean_ctor_set(x_194, 1, x_171);
x_195 = l_Lean_Expr_const___override(x_193, x_194);
x_196 = lean_box(0);
x_197 = l_Lean_Expr_sort___override(x_196);
x_198 = l_Lean_Expr_getAppNumArgs(x_167);
lean_inc(x_198);
x_199 = lean_mk_array(x_198, x_197);
x_200 = lean_unsigned_to_nat(1u);
x_201 = lean_nat_sub(x_198, x_200);
lean_dec(x_198);
x_202 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_167, x_199, x_201);
x_203 = lean_unsigned_to_nat(4u);
x_204 = lean_mk_empty_array_with_capacity(x_203);
x_205 = lean_array_push(x_204, x_1);
x_206 = lean_array_push(x_205, x_188);
x_207 = lean_array_push(x_206, x_189);
x_208 = lean_array_push(x_207, x_2);
x_209 = l_Array_append(lean_box(0), x_202, x_208);
lean_dec(x_208);
x_210 = l_Lean_mkAppN(x_195, x_209);
lean_dec(x_209);
if (lean_is_scalar(x_187)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_187;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_186);
return x_211;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_183);
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_167);
lean_dec(x_163);
lean_dec(x_149);
lean_dec(x_2);
lean_dec(x_1);
x_212 = lean_ctor_get(x_184, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_184, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_214 = x_184;
} else {
 lean_dec_ref(x_184);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_213);
return x_215;
}
}
else
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_182);
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_163);
lean_dec(x_149);
lean_dec(x_2);
lean_dec(x_1);
x_216 = lean_box(0);
x_217 = l_Lean_Meta_mkNoConfusion___lam__0(x_167, x_216, x_3, x_4, x_5, x_6, x_174);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_217;
}
}
}
else
{
lean_object* x_218; lean_object* x_219; 
lean_dec(x_169);
lean_dec(x_163);
lean_dec(x_149);
lean_dec(x_2);
lean_dec(x_1);
x_218 = lean_box(0);
x_219 = l_Lean_Meta_mkNoConfusion___lam__0(x_167, x_218, x_3, x_4, x_5, x_6, x_168);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_219;
}
}
else
{
lean_dec(x_163);
lean_dec(x_149);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_166;
}
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkNoConfusion___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_mk_string_unchecked("Pure", 4, 4);
x_9 = lean_mk_string_unchecked("pure", 4, 4);
x_10 = l_Lean_Name_mkStr2(x_8, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_2);
x_14 = lean_unsigned_to_nat(4u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_11);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_12);
x_19 = lean_array_push(x_18, x_13);
x_20 = l_Lean_Meta_mkAppOptM(x_10, x_19, x_3, x_4, x_5, x_6, x_7);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkProjection_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkProjection_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_usize_dec_lt(x_7, x_6);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_24; lean_object* x_25; lean_object* x_32; lean_object* x_33; 
lean_dec(x_8);
x_17 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_17);
x_32 = lean_array_uget(x_5, x_7);
lean_inc(x_32);
lean_inc(x_2);
lean_inc(x_1);
x_33 = l_Lean_isSubobjectField_x3f(x_1, x_2, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_dec(x_32);
x_34 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkProjection_spec__0___lam__0(x_17, x_9, x_10, x_11, x_12, x_13);
x_25 = x_34;
goto block_31;
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_3);
x_37 = l_Lean_Meta_mkProjection(x_3, x_32, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Meta_saveState___redArg(x_10, x_11, x_12, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_43 = l_Lean_Meta_mkProjection(x_38, x_4, x_9, x_10, x_11, x_12, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_41);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_ctor_set(x_33, 0, x_44);
x_18 = x_33;
x_19 = x_45;
goto block_23;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_55; 
lean_free_object(x_33);
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_48 = x_43;
} else {
 lean_dec_ref(x_43);
 x_48 = lean_box(0);
}
x_55 = l_Lean_Exception_isInterrupt(x_46);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = l_Lean_Exception_isRuntime(x_46);
x_49 = x_56;
goto block_54;
}
else
{
x_49 = x_55;
goto block_54;
}
block_54:
{
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_48);
lean_dec(x_46);
x_50 = l_Lean_Meta_SavedState_restore___redArg(x_41, x_10, x_12, x_47);
lean_dec(x_41);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkProjection_spec__0___lam__0(x_17, x_9, x_10, x_11, x_12, x_51);
x_25 = x_52;
goto block_31;
}
else
{
lean_object* x_53; 
lean_dec(x_41);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_48)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_48;
}
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_47);
return x_53;
}
}
}
}
else
{
uint8_t x_57; 
lean_free_object(x_33);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_37);
if (x_57 == 0)
{
return x_37;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_37, 0);
x_59 = lean_ctor_get(x_37, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_37);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; 
lean_dec(x_33);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_3);
x_61 = l_Lean_Meta_mkProjection(x_3, x_32, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Meta_saveState___redArg(x_10, x_11, x_12, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_67 = l_Lean_Meta_mkProjection(x_62, x_4, x_9, x_10, x_11, x_12, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_68);
x_18 = x_70;
x_19 = x_69;
goto block_23;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_80; 
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_73 = x_67;
} else {
 lean_dec_ref(x_67);
 x_73 = lean_box(0);
}
x_80 = l_Lean_Exception_isInterrupt(x_71);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = l_Lean_Exception_isRuntime(x_71);
x_74 = x_81;
goto block_79;
}
else
{
x_74 = x_80;
goto block_79;
}
block_79:
{
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_73);
lean_dec(x_71);
x_75 = l_Lean_Meta_SavedState_restore___redArg(x_65, x_10, x_12, x_72);
lean_dec(x_65);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkProjection_spec__0___lam__0(x_17, x_9, x_10, x_11, x_12, x_76);
x_25 = x_77;
goto block_31;
}
else
{
lean_object* x_78; 
lean_dec(x_65);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_73)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_73;
}
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_72);
return x_78;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = lean_ctor_get(x_61, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_61, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_84 = x_61;
} else {
 lean_dec_ref(x_61);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
block_23:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
block_31:
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_usize_of_nat(x_27);
x_29 = lean_usize_add(x_7, x_28);
x_7 = x_29;
x_8 = x_24;
x_13 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_mk_string_unchecked("mkProjection", 12, 12);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked("structure expected", 18, 18);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_MessageData_ofFormat(x_12);
x_14 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_2);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_10, x_15, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_mkProjection___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = lean_whnf(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_16 = l_Lean_Expr_getAppFn(x_13);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_2);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Expr_bvar___override(x_17);
x_19 = l_Lean_Meta_mkProjection___lam__0(x_1, x_13, x_18, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_18);
return x_19;
}
case 1:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_2);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Lean_Expr_fvar___override(x_20);
x_22 = l_Lean_Meta_mkProjection___lam__0(x_1, x_13, x_21, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_21);
return x_22;
}
case 2:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_2);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = l_Lean_Expr_mvar___override(x_23);
x_25 = l_Lean_Meta_mkProjection___lam__0(x_1, x_13, x_24, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_24);
return x_25;
}
case 3:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_2);
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
lean_dec(x_16);
x_27 = l_Lean_Expr_sort___override(x_26);
x_28 = l_Lean_Meta_mkProjection___lam__0(x_1, x_13, x_27, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_27);
return x_28;
}
case 4:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_103; 
x_29 = lean_ctor_get(x_16, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_dec(x_16);
x_31 = lean_st_ref_get(x_6, x_14);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_closure((void*)(l_Lean_Meta_mkProjection___lam__1___boxed), 1, 0);
x_60 = lean_ctor_get(x_32, 0);
lean_inc(x_60);
lean_dec(x_32);
lean_inc(x_29);
lean_inc(x_60);
x_103 = l_Lean_isStructure(x_60, x_29);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_60);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_2);
x_104 = lean_mk_string_unchecked("mkProjection", 12, 12);
x_105 = l_Lean_Name_mkStr1(x_104);
x_106 = lean_mk_string_unchecked("structure expected", 18, 18);
x_107 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = l_Lean_MessageData_ofFormat(x_107);
x_109 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_13);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_105, x_110, x_3, x_4, x_5, x_6, x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
return x_111;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_111, 0);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_111);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
else
{
x_61 = x_3;
x_62 = x_4;
x_63 = x_5;
x_64 = x_6;
x_65 = x_33;
goto block_102;
}
block_59:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_41 = lean_mk_string_unchecked("mkProjection", 12, 12);
x_42 = l_Lean_Name_mkStr1(x_41);
x_43 = lean_mk_string_unchecked("invalid field name '", 20, 20);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Lean_MessageData_ofFormat(x_44);
x_46 = lean_box(1);
x_47 = lean_unbox(x_46);
x_48 = l_Lean_Name_toString(x_2, x_47, x_35);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_MessageData_ofFormat(x_49);
if (lean_is_scalar(x_15)) {
 x_51 = lean_alloc_ctor(7, 2, 0);
} else {
 x_51 = x_15;
 lean_ctor_set_tag(x_51, 7);
}
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_mk_string_unchecked("' for", 5, 5);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_MessageData_ofFormat(x_53);
if (lean_is_scalar(x_11)) {
 x_55 = lean_alloc_ctor(7, 2, 0);
} else {
 x_55 = x_11;
 lean_ctor_set_tag(x_55, 7);
}
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
x_56 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_13);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(x_42, x_57, x_37, x_36, x_38, x_39, x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_37);
return x_58;
}
block_102:
{
lean_object* x_66; 
lean_inc(x_2);
lean_inc(x_29);
lean_inc(x_60);
x_66 = l_Lean_getProjFnForField_x3f(x_60, x_29, x_2);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; lean_object* x_72; size_t x_73; lean_object* x_74; 
lean_dec(x_34);
lean_dec(x_30);
lean_inc(x_29);
lean_inc(x_60);
x_67 = l_Lean_getStructureFields(x_60, x_29);
x_68 = lean_box(0);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_array_size(x_67);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_usize_of_nat(x_72);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_2);
lean_inc(x_1);
x_74 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkProjection_spec__0(x_60, x_29, x_1, x_2, x_67, x_71, x_73, x_70, x_61, x_62, x_63, x_64, x_65);
lean_dec(x_67);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec(x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_36 = x_62;
x_37 = x_61;
x_38 = x_63;
x_39 = x_64;
x_40 = x_77;
goto block_59;
}
else
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
lean_dec(x_76);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
lean_dec(x_74);
x_36 = x_62;
x_37 = x_61;
x_38 = x_63;
x_39 = x_64;
x_40 = x_79;
goto block_59;
}
else
{
uint8_t x_80; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_35);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_74);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_74, 0);
lean_dec(x_81);
x_82 = lean_ctor_get(x_78, 0);
lean_inc(x_82);
lean_dec(x_78);
lean_ctor_set(x_74, 0, x_82);
return x_74;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_74, 1);
lean_inc(x_83);
lean_dec(x_74);
x_84 = lean_ctor_get(x_78, 0);
lean_inc(x_84);
lean_dec(x_78);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_35);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_74);
if (x_86 == 0)
{
return x_74;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_74, 0);
x_88 = lean_ctor_get(x_74, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_74);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_35);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_2);
x_90 = lean_ctor_get(x_66, 0);
lean_inc(x_90);
lean_dec(x_66);
x_91 = lean_box(0);
x_92 = l_Lean_Expr_sort___override(x_91);
x_93 = l_Lean_Expr_getAppNumArgs(x_13);
lean_inc(x_93);
x_94 = lean_mk_array(x_93, x_92);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_sub(x_93, x_95);
lean_dec(x_93);
x_97 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_13, x_94, x_96);
x_98 = l_Lean_Expr_const___override(x_90, x_30);
x_99 = l_Lean_mkAppN(x_98, x_97);
lean_dec(x_97);
x_100 = l_Lean_Expr_app___override(x_99, x_1);
if (lean_is_scalar(x_34)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_34;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_65);
return x_101;
}
}
}
case 5:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_2);
x_116 = lean_ctor_get(x_16, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_16, 1);
lean_inc(x_117);
lean_dec(x_16);
x_118 = l_Lean_Expr_app___override(x_116, x_117);
x_119 = l_Lean_Meta_mkProjection___lam__0(x_1, x_13, x_118, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_118);
return x_119;
}
case 6:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_2);
x_120 = lean_ctor_get(x_16, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_16, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_16, 2);
lean_inc(x_122);
x_123 = lean_ctor_get_uint8(x_16, sizeof(void*)*3 + 8);
lean_dec(x_16);
x_124 = l_Lean_Expr_lam___override(x_120, x_121, x_122, x_123);
x_125 = l_Lean_Meta_mkProjection___lam__0(x_1, x_13, x_124, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_124);
return x_125;
}
case 7:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_2);
x_126 = lean_ctor_get(x_16, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_16, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_16, 2);
lean_inc(x_128);
x_129 = lean_ctor_get_uint8(x_16, sizeof(void*)*3 + 8);
lean_dec(x_16);
x_130 = l_Lean_Expr_forallE___override(x_126, x_127, x_128, x_129);
x_131 = l_Lean_Meta_mkProjection___lam__0(x_1, x_13, x_130, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_130);
return x_131;
}
case 8:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_2);
x_132 = lean_ctor_get(x_16, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_16, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_16, 2);
lean_inc(x_134);
x_135 = lean_ctor_get(x_16, 3);
lean_inc(x_135);
x_136 = lean_ctor_get_uint8(x_16, sizeof(void*)*4 + 8);
lean_dec(x_16);
x_137 = l_Lean_Expr_letE___override(x_132, x_133, x_134, x_135, x_136);
x_138 = l_Lean_Meta_mkProjection___lam__0(x_1, x_13, x_137, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_137);
return x_138;
}
case 9:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_2);
x_139 = lean_ctor_get(x_16, 0);
lean_inc(x_139);
lean_dec(x_16);
x_140 = l_Lean_Expr_lit___override(x_139);
x_141 = l_Lean_Meta_mkProjection___lam__0(x_1, x_13, x_140, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_140);
return x_141;
}
case 10:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_2);
x_142 = lean_ctor_get(x_16, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_16, 1);
lean_inc(x_143);
lean_dec(x_16);
x_144 = l_Lean_Expr_mdata___override(x_142, x_143);
x_145 = l_Lean_Meta_mkProjection___lam__0(x_1, x_13, x_144, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_144);
return x_145;
}
default: 
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_2);
x_146 = lean_ctor_get(x_16, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_16, 1);
lean_inc(x_147);
x_148 = lean_ctor_get(x_16, 2);
lean_inc(x_148);
lean_dec(x_16);
x_149 = l_Lean_Expr_proj___override(x_146, x_147, x_148);
x_150 = l_Lean_Meta_mkProjection___lam__0(x_1, x_13, x_149, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_149);
return x_150;
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkProjection_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkProjection_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkProjection_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkProjection_spec__0(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkProjection___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___lam__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_mkProjection___lam__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_2);
x_6 = l_Lean_Expr_app___override(x_2, x_4);
x_7 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(x_1, x_2, x_5);
x_8 = l_Lean_Expr_app___override(x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Meta_getDecLevel(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_mk_string_unchecked("List", 4, 4);
x_12 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_11);
x_13 = l_Lean_Name_mkStr2(x_11, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
lean_inc(x_15);
x_16 = l_Lean_Expr_const___override(x_13, x_15);
lean_inc(x_1);
x_17 = l_Lean_Expr_app___override(x_16, x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_1);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_mk_string_unchecked("cons", 4, 4);
x_19 = l_Lean_Name_mkStr2(x_11, x_18);
x_20 = l_Lean_Expr_const___override(x_19, x_15);
x_21 = l_Lean_Expr_app___override(x_20, x_1);
x_22 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(x_17, x_21, x_2);
lean_dec(x_17);
lean_ctor_set(x_8, 0, x_22);
return x_8;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_25 = lean_mk_string_unchecked("List", 4, 4);
x_26 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_25);
x_27 = l_Lean_Name_mkStr2(x_25, x_26);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_28);
lean_inc(x_29);
x_30 = l_Lean_Expr_const___override(x_27, x_29);
lean_inc(x_1);
x_31 = l_Lean_Expr_app___override(x_30, x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_mk_string_unchecked("cons", 4, 4);
x_34 = l_Lean_Name_mkStr2(x_25, x_33);
x_35 = l_Lean_Expr_const___override(x_34, x_29);
x_36 = l_Lean_Expr_app___override(x_35, x_1);
x_37 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(x_31, x_36, x_2);
lean_dec(x_31);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_24);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_8);
if (x_39 == 0)
{
return x_8;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_8, 0);
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_8);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_getDecLevel(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = l_Lean_Meta_mkListLit(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_mk_string_unchecked("List", 4, 4);
x_15 = lean_mk_string_unchecked("toArray", 7, 7);
x_16 = l_Lean_Name_mkStr2(x_14, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Expr_const___override(x_16, x_18);
x_20 = l_Lean_Expr_app___override(x_19, x_1);
x_21 = l_Lean_Expr_app___override(x_20, x_13);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_mk_string_unchecked("List", 4, 4);
x_25 = lean_mk_string_unchecked("toArray", 7, 7);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Expr_const___override(x_26, x_28);
x_30 = l_Lean_Expr_app___override(x_29, x_1);
x_31 = l_Lean_Expr_app___override(x_30, x_22);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_23);
return x_32;
}
}
else
{
lean_dec(x_9);
lean_dec(x_1);
return x_11;
}
}
else
{
uint8_t x_33; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_8);
if (x_33 == 0)
{
return x_8;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_8, 0);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_8);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_getDecLevel(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_mk_string_unchecked("Option", 6, 6);
x_11 = lean_mk_string_unchecked("none", 4, 4);
x_12 = l_Lean_Name_mkStr2(x_10, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Expr_const___override(x_12, x_14);
x_16 = l_Lean_Expr_app___override(x_15, x_1);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_mk_string_unchecked("Option", 6, 6);
x_20 = lean_mk_string_unchecked("none", 4, 4);
x_21 = l_Lean_Name_mkStr2(x_19, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Expr_const___override(x_21, x_23);
x_25 = l_Lean_Expr_app___override(x_24, x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_18);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
return x_7;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_7);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Meta_getDecLevel(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_mk_string_unchecked("Option", 6, 6);
x_12 = lean_mk_string_unchecked("some", 4, 4);
x_13 = l_Lean_Name_mkStr2(x_11, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Expr_const___override(x_13, x_15);
x_17 = l_Lean_mkAppB(x_16, x_1, x_2);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_mk_string_unchecked("Option", 6, 6);
x_21 = lean_mk_string_unchecked("some", 4, 4);
x_22 = l_Lean_Name_mkStr2(x_20, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Expr_const___override(x_22, x_24);
x_26 = l_Lean_mkAppB(x_25, x_1, x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_8);
if (x_28 == 0)
{
return x_8;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_8, 0);
x_30 = lean_ctor_get(x_8, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_8);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_mk_string_unchecked("Decidable", 9, 9);
x_8 = lean_mk_string_unchecked("decide", 6, 6);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_box(0);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_14 = lean_array_push(x_13, x_10);
x_15 = lean_array_push(x_14, x_11);
x_16 = l_Lean_Meta_mkAppOptM(x_9, x_15, x_2, x_3, x_4, x_5, x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_mkDecide(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_mk_string_unchecked("Bool", 4, 4);
x_11 = lean_mk_string_unchecked("true", 4, 4);
x_12 = l_Lean_Name_mkStr2(x_10, x_11);
x_13 = lean_box(0);
x_14 = l_Lean_Expr_const___override(x_12, x_13);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_14);
x_15 = l_Lean_Meta_mkEq(x_8, x_14, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_Meta_mkEqRefl(x_14, x_2, x_3, x_4, x_5, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_mkExpectedPropHint(x_19, x_16);
x_22 = lean_mk_string_unchecked("of_decide_eq_true", 17, 17);
x_23 = l_Lean_Name_mkStr1(x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_mk_empty_array_with_capacity(x_24);
x_26 = lean_array_push(x_25, x_21);
x_27 = l_Lean_Meta_mkAppM(x_23, x_26, x_2, x_3, x_4, x_5, x_20);
return x_27;
}
else
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
}
else
{
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_mk_string_unchecked("LT", 2, 2);
x_9 = lean_mk_string_unchecked("lt", 2, 2);
x_10 = l_Lean_Name_mkStr2(x_8, x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_mk_empty_array_with_capacity(x_11);
x_13 = lean_array_push(x_12, x_1);
x_14 = lean_array_push(x_13, x_2);
x_15 = l_Lean_Meta_mkAppM(x_10, x_14, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_mk_string_unchecked("LE", 2, 2);
x_9 = lean_mk_string_unchecked("le", 2, 2);
x_10 = l_Lean_Name_mkStr2(x_8, x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_mk_empty_array_with_capacity(x_11);
x_13 = lean_array_push(x_12, x_1);
x_14 = lean_array_push(x_13, x_2);
x_15 = l_Lean_Meta_mkAppM(x_10, x_14, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_mk_string_unchecked("Inhabited", 9, 9);
x_8 = lean_mk_string_unchecked("default", 7, 7);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_box(0);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_14 = lean_array_push(x_13, x_10);
x_15 = lean_array_push(x_14, x_11);
x_16 = l_Lean_Meta_mkAppOptM(x_9, x_15, x_2, x_3, x_4, x_5, x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_mk_string_unchecked("Classical", 9, 9);
x_8 = lean_mk_string_unchecked("ofNonempty", 10, 10);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_box(0);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_14 = lean_array_push(x_13, x_10);
x_15 = lean_array_push(x_14, x_11);
x_16 = l_Lean_Meta_mkAppOptM(x_9, x_15, x_2, x_3, x_4, x_5, x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_mk_string_unchecked("funext", 6, 6);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
x_11 = lean_array_push(x_10, x_1);
x_12 = l_Lean_Meta_mkAppM(x_8, x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_mk_string_unchecked("propext", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
x_11 = lean_array_push(x_10, x_1);
x_12 = l_Lean_Meta_mkAppM(x_8, x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_mk_string_unchecked("let_congr", 9, 9);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = lean_array_push(x_11, x_1);
x_13 = lean_array_push(x_12, x_2);
x_14 = l_Lean_Meta_mkAppM(x_9, x_13, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_mk_string_unchecked("let_val_congr", 13, 13);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = lean_array_push(x_11, x_1);
x_13 = lean_array_push(x_12, x_2);
x_14 = l_Lean_Meta_mkAppM(x_9, x_13, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_mk_string_unchecked("let_body_congr", 14, 14);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = lean_array_push(x_11, x_1);
x_13 = lean_array_push(x_12, x_2);
x_14 = l_Lean_Meta_mkAppM(x_9, x_13, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_9; uint8_t x_10; 
lean_inc(x_2);
x_9 = l_Lean_Expr_cleanupAnnotations(x_2);
x_10 = l_Lean_Expr_isApp(x_9);
if (x_10 == 0)
{
lean_dec(x_9);
goto block_8;
}
else
{
lean_object* x_11; uint8_t x_12; 
lean_inc(x_9);
x_11 = l_Lean_Expr_appFnCleanup___redArg(x_9);
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_dec(x_11);
lean_dec(x_9);
goto block_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l_Lean_Expr_appFnCleanup___redArg(x_11);
x_14 = lean_mk_string_unchecked("eq_false", 8, 8);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = l_Lean_Expr_isConstOf(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
if (x_16 == 0)
{
lean_dec(x_9);
goto block_8;
}
else
{
lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
return x_17;
}
}
}
block_8:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_mk_string_unchecked("of_eq_false", 11, 11);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
x_7 = l_Lean_mkAppB(x_6, x_1, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
lean_inc(x_1);
x_7 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_3, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_22; uint8_t x_23; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_22 = l_Lean_Expr_cleanupAnnotations(x_9);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_free_object(x_7);
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
goto block_21;
}
else
{
lean_object* x_24; uint8_t x_25; 
lean_inc(x_22);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_22);
lean_free_object(x_7);
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
goto block_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_27 = lean_mk_string_unchecked("eq_false", 8, 8);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = l_Lean_Expr_isConstOf(x_26, x_28);
lean_dec(x_28);
lean_dec(x_26);
if (x_29 == 0)
{
lean_dec(x_22);
lean_free_object(x_7);
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
goto block_21;
}
else
{
lean_object* x_30; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
lean_ctor_set(x_7, 0, x_30);
return x_7;
}
}
}
block_21:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_mk_string_unchecked("of_eq_false", 11, 11);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_mk_empty_array_with_capacity(x_17);
x_19 = lean_array_push(x_18, x_1);
x_20 = l_Lean_Meta_mkAppM(x_16, x_19, x_11, x_12, x_13, x_14, x_10);
return x_20;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_44; uint8_t x_45; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_44 = l_Lean_Expr_cleanupAnnotations(x_31);
x_45 = l_Lean_Expr_isApp(x_44);
if (x_45 == 0)
{
lean_dec(x_44);
x_33 = x_2;
x_34 = x_3;
x_35 = x_4;
x_36 = x_5;
goto block_43;
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_inc(x_44);
x_46 = l_Lean_Expr_appFnCleanup___redArg(x_44);
x_47 = l_Lean_Expr_isApp(x_46);
if (x_47 == 0)
{
lean_dec(x_46);
lean_dec(x_44);
x_33 = x_2;
x_34 = x_3;
x_35 = x_4;
x_36 = x_5;
goto block_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = l_Lean_Expr_appFnCleanup___redArg(x_46);
x_49 = lean_mk_string_unchecked("eq_false", 8, 8);
x_50 = l_Lean_Name_mkStr1(x_49);
x_51 = l_Lean_Expr_isConstOf(x_48, x_50);
lean_dec(x_50);
lean_dec(x_48);
if (x_51 == 0)
{
lean_dec(x_44);
x_33 = x_2;
x_34 = x_3;
x_35 = x_4;
x_36 = x_5;
goto block_43;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_dec(x_44);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_32);
return x_53;
}
}
}
block_43:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_mk_string_unchecked("of_eq_false", 11, 11);
x_38 = l_Lean_Name_mkStr1(x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_mk_empty_array_with_capacity(x_39);
x_41 = lean_array_push(x_40, x_1);
x_42 = l_Lean_Meta_mkAppM(x_38, x_41, x_33, x_34, x_35, x_36, x_32);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_9; uint8_t x_10; 
lean_inc(x_2);
x_9 = l_Lean_Expr_cleanupAnnotations(x_2);
x_10 = l_Lean_Expr_isApp(x_9);
if (x_10 == 0)
{
lean_dec(x_9);
goto block_8;
}
else
{
lean_object* x_11; uint8_t x_12; 
lean_inc(x_9);
x_11 = l_Lean_Expr_appFnCleanup___redArg(x_9);
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_dec(x_11);
lean_dec(x_9);
goto block_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l_Lean_Expr_appFnCleanup___redArg(x_11);
x_14 = lean_mk_string_unchecked("eq_true", 7, 7);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = l_Lean_Expr_isConstOf(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
if (x_16 == 0)
{
lean_dec(x_9);
goto block_8;
}
else
{
lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
return x_17;
}
}
}
block_8:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_mk_string_unchecked("of_eq_true", 10, 10);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
x_7 = l_Lean_mkAppB(x_6, x_1, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
lean_inc(x_1);
x_7 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_3, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_22; uint8_t x_23; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_22 = l_Lean_Expr_cleanupAnnotations(x_9);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_free_object(x_7);
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
goto block_21;
}
else
{
lean_object* x_24; uint8_t x_25; 
lean_inc(x_22);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_22);
lean_free_object(x_7);
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
goto block_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_27 = lean_mk_string_unchecked("eq_true", 7, 7);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = l_Lean_Expr_isConstOf(x_26, x_28);
lean_dec(x_28);
lean_dec(x_26);
if (x_29 == 0)
{
lean_dec(x_22);
lean_free_object(x_7);
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
goto block_21;
}
else
{
lean_object* x_30; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
lean_ctor_set(x_7, 0, x_30);
return x_7;
}
}
}
block_21:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_mk_string_unchecked("of_eq_true", 10, 10);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_mk_empty_array_with_capacity(x_17);
x_19 = lean_array_push(x_18, x_1);
x_20 = l_Lean_Meta_mkAppM(x_16, x_19, x_11, x_12, x_13, x_14, x_10);
return x_20;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_44; uint8_t x_45; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_44 = l_Lean_Expr_cleanupAnnotations(x_31);
x_45 = l_Lean_Expr_isApp(x_44);
if (x_45 == 0)
{
lean_dec(x_44);
x_33 = x_2;
x_34 = x_3;
x_35 = x_4;
x_36 = x_5;
goto block_43;
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_inc(x_44);
x_46 = l_Lean_Expr_appFnCleanup___redArg(x_44);
x_47 = l_Lean_Expr_isApp(x_46);
if (x_47 == 0)
{
lean_dec(x_46);
lean_dec(x_44);
x_33 = x_2;
x_34 = x_3;
x_35 = x_4;
x_36 = x_5;
goto block_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = l_Lean_Expr_appFnCleanup___redArg(x_46);
x_49 = lean_mk_string_unchecked("eq_true", 7, 7);
x_50 = l_Lean_Name_mkStr1(x_49);
x_51 = l_Lean_Expr_isConstOf(x_48, x_50);
lean_dec(x_50);
lean_dec(x_48);
if (x_51 == 0)
{
lean_dec(x_44);
x_33 = x_2;
x_34 = x_3;
x_35 = x_4;
x_36 = x_5;
goto block_43;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_dec(x_44);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_32);
return x_53;
}
}
}
block_43:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_mk_string_unchecked("of_eq_true", 10, 10);
x_38 = l_Lean_Name_mkStr1(x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_mk_empty_array_with_capacity(x_39);
x_41 = lean_array_push(x_40, x_1);
x_42 = l_Lean_Meta_mkAppM(x_38, x_41, x_33, x_34, x_35, x_36, x_32);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrueCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_9; uint8_t x_10; 
lean_inc(x_2);
x_9 = l_Lean_Expr_cleanupAnnotations(x_2);
x_10 = l_Lean_Expr_isApp(x_9);
if (x_10 == 0)
{
lean_dec(x_9);
goto block_8;
}
else
{
lean_object* x_11; uint8_t x_12; 
lean_inc(x_9);
x_11 = l_Lean_Expr_appFnCleanup___redArg(x_9);
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_dec(x_11);
lean_dec(x_9);
goto block_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l_Lean_Expr_appFnCleanup___redArg(x_11);
x_14 = lean_mk_string_unchecked("of_eq_true", 10, 10);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = l_Lean_Expr_isConstOf(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
if (x_16 == 0)
{
lean_dec(x_9);
goto block_8;
}
else
{
lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
return x_17;
}
}
}
block_8:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_mk_string_unchecked("eq_true", 7, 7);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
x_7 = l_Lean_mkAppB(x_6, x_1, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
lean_inc(x_1);
x_7 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_3, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_32; uint8_t x_33; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_32 = l_Lean_Expr_cleanupAnnotations(x_9);
x_33 = l_Lean_Expr_isApp(x_32);
if (x_33 == 0)
{
lean_dec(x_32);
lean_free_object(x_7);
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
goto block_31;
}
else
{
lean_object* x_34; uint8_t x_35; 
lean_inc(x_32);
x_34 = l_Lean_Expr_appFnCleanup___redArg(x_32);
x_35 = l_Lean_Expr_isApp(x_34);
if (x_35 == 0)
{
lean_dec(x_34);
lean_dec(x_32);
lean_free_object(x_7);
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
goto block_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = l_Lean_Expr_appFnCleanup___redArg(x_34);
x_37 = lean_mk_string_unchecked("of_eq_true", 10, 10);
x_38 = l_Lean_Name_mkStr1(x_37);
x_39 = l_Lean_Expr_isConstOf(x_36, x_38);
lean_dec(x_38);
lean_dec(x_36);
if (x_39 == 0)
{
lean_dec(x_32);
lean_free_object(x_7);
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
goto block_31;
}
else
{
lean_object* x_40; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_dec(x_32);
lean_ctor_set(x_7, 0, x_40);
return x_7;
}
}
}
block_31:
{
lean_object* x_15; 
lean_inc(x_1);
x_15 = lean_infer_type(x_1, x_11, x_12, x_13, x_14, x_10);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_mk_string_unchecked("eq_true", 7, 7);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = lean_box(0);
x_21 = l_Lean_Expr_const___override(x_19, x_20);
x_22 = l_Lean_mkAppB(x_21, x_17, x_1);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_mk_string_unchecked("eq_true", 7, 7);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_box(0);
x_28 = l_Lean_Expr_const___override(x_26, x_27);
x_29 = l_Lean_mkAppB(x_28, x_23, x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
else
{
lean_dec(x_1);
return x_15;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_58; uint8_t x_59; 
x_41 = lean_ctor_get(x_7, 0);
x_42 = lean_ctor_get(x_7, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_7);
x_58 = l_Lean_Expr_cleanupAnnotations(x_41);
x_59 = l_Lean_Expr_isApp(x_58);
if (x_59 == 0)
{
lean_dec(x_58);
x_43 = x_2;
x_44 = x_3;
x_45 = x_4;
x_46 = x_5;
goto block_57;
}
else
{
lean_object* x_60; uint8_t x_61; 
lean_inc(x_58);
x_60 = l_Lean_Expr_appFnCleanup___redArg(x_58);
x_61 = l_Lean_Expr_isApp(x_60);
if (x_61 == 0)
{
lean_dec(x_60);
lean_dec(x_58);
x_43 = x_2;
x_44 = x_3;
x_45 = x_4;
x_46 = x_5;
goto block_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = l_Lean_Expr_appFnCleanup___redArg(x_60);
x_63 = lean_mk_string_unchecked("of_eq_true", 10, 10);
x_64 = l_Lean_Name_mkStr1(x_63);
x_65 = l_Lean_Expr_isConstOf(x_62, x_64);
lean_dec(x_64);
lean_dec(x_62);
if (x_65 == 0)
{
lean_dec(x_58);
x_43 = x_2;
x_44 = x_3;
x_45 = x_4;
x_46 = x_5;
goto block_57;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = lean_ctor_get(x_58, 1);
lean_inc(x_66);
lean_dec(x_58);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_42);
return x_67;
}
}
}
block_57:
{
lean_object* x_47; 
lean_inc(x_1);
x_47 = lean_infer_type(x_1, x_43, x_44, x_45, x_46, x_42);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = lean_mk_string_unchecked("eq_true", 7, 7);
x_52 = l_Lean_Name_mkStr1(x_51);
x_53 = lean_box(0);
x_54 = l_Lean_Expr_const___override(x_52, x_53);
x_55 = l_Lean_mkAppB(x_54, x_48, x_1);
if (lean_is_scalar(x_50)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_50;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_49);
return x_56;
}
else
{
lean_dec(x_1);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_19; uint8_t x_20; 
lean_inc(x_1);
x_19 = l_Lean_Expr_cleanupAnnotations(x_1);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
x_7 = x_2;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
goto block_18;
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_inc(x_19);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_19);
x_7 = x_2;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
goto block_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = lean_mk_string_unchecked("of_eq_false", 11, 11);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = l_Lean_Expr_isConstOf(x_23, x_25);
lean_dec(x_25);
lean_dec(x_23);
if (x_26 == 0)
{
lean_dec(x_19);
x_7 = x_2;
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
goto block_18;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
}
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_mk_string_unchecked("eq_false", 8, 8);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_1);
x_17 = l_Lean_Meta_mkAppM(x_13, x_16, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_mk_string_unchecked("eq_false'", 9, 9);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
x_11 = lean_array_push(x_10, x_1);
x_12 = l_Lean_Meta_mkAppM(x_8, x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_mk_string_unchecked("implies_congr", 13, 13);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = lean_array_push(x_11, x_1);
x_13 = lean_array_push(x_12, x_2);
x_14 = l_Lean_Meta_mkAppM(x_9, x_13, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_mk_string_unchecked("implies_congr_ctx", 17, 17);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = lean_array_push(x_11, x_1);
x_13 = lean_array_push(x_12, x_2);
x_14 = l_Lean_Meta_mkAppM(x_9, x_13, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_mk_string_unchecked("implies_dep_congr_ctx", 21, 21);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = lean_array_push(x_11, x_1);
x_13 = lean_array_push(x_12, x_2);
x_14 = l_Lean_Meta_mkAppM(x_9, x_13, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_mk_string_unchecked("forall_congr", 12, 12);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
x_11 = lean_array_push(x_10, x_1);
x_12 = l_Lean_Meta_mkAppM(x_8, x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_14; lean_object* x_15; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_mk_string_unchecked("Monad", 5, 5);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_mk_empty_array_with_capacity(x_21);
x_23 = lean_array_push(x_22, x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_24 = l_Lean_Meta_mkAppM(x_20, x_23, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = l_Lean_Meta_trySynthInstance(x_25, x_27, x_2, x_3, x_4, x_5, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 1)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_28, 0, x_34);
return x_28;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_ctor_get(x_29, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_37 = x_29;
} else {
 lean_dec_ref(x_29);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 1, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_29);
x_40 = !lean_is_exclusive(x_28);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_28, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_28, 0, x_42);
return x_28;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
lean_dec(x_28);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_28, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_28, 1);
lean_inc(x_47);
lean_dec(x_28);
x_14 = x_46;
x_15 = x_47;
goto block_18;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = lean_ctor_get(x_24, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_24, 1);
lean_inc(x_49);
lean_dec(x_24);
x_14 = x_48;
x_15 = x_49;
goto block_18;
}
block_13:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
block_18:
{
uint8_t x_16; 
x_16 = l_Lean_Exception_isInterrupt(x_14);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_Exception_isRuntime(x_14);
x_7 = x_14;
x_8 = x_15;
x_9 = x_17;
goto block_13;
}
else
{
x_7 = x_14;
x_8 = x_15;
x_9 = x_16;
goto block_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_getDecLevel(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_mk_string_unchecked("OfNat", 5, 5);
lean_inc(x_11);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_14);
x_15 = l_Lean_Expr_const___override(x_12, x_14);
x_16 = l_Lean_mkRawNatLit(x_2);
lean_inc(x_16);
lean_inc(x_1);
x_17 = l_Lean_mkAppB(x_15, x_1, x_16);
x_18 = lean_box(0);
x_19 = l_Lean_Meta_synthInstance(x_17, x_18, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_mk_string_unchecked("ofNat", 5, 5);
x_23 = l_Lean_Name_mkStr2(x_11, x_22);
x_24 = l_Lean_Expr_const___override(x_23, x_14);
x_25 = l_Lean_mkApp3(x_24, x_1, x_16, x_21);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_mk_string_unchecked("ofNat", 5, 5);
x_29 = l_Lean_Name_mkStr2(x_11, x_28);
x_30 = l_Lean_Expr_const___override(x_29, x_14);
x_31 = l_Lean_mkApp3(x_30, x_1, x_16, x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
}
else
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_1);
return x_19;
}
}
else
{
uint8_t x_33; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_8);
if (x_33 == 0)
{
return x_8;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_8, 0);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_8);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_10 = lean_infer_type(x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_12);
x_14 = l_Lean_Meta_getDecLevel(x_12, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
lean_inc(x_15);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 1, x_17);
lean_ctor_set(x_10, 0, x_15);
lean_inc(x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_19);
x_20 = l_Lean_Expr_const___override(x_1, x_19);
lean_inc_n(x_12, 3);
x_21 = l_Lean_mkApp3(x_20, x_12, x_12, x_12);
x_22 = lean_box(0);
x_23 = l_Lean_Meta_synthInstance(x_21, x_22, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_Lean_Expr_const___override(x_2, x_19);
lean_inc_n(x_12, 2);
x_27 = l_Lean_mkApp6(x_26, x_12, x_12, x_12, x_25, x_3, x_4);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = l_Lean_Expr_const___override(x_2, x_19);
lean_inc_n(x_12, 2);
x_31 = l_Lean_mkApp6(x_30, x_12, x_12, x_12, x_28, x_3, x_4);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_23;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_10);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
return x_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_10, 0);
x_38 = lean_ctor_get(x_10, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_37);
x_39 = l_Lean_Meta_getDecLevel(x_37, x_5, x_6, x_7, x_8, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_box(0);
lean_inc(x_40);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
lean_inc(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_44);
lean_inc(x_45);
x_46 = l_Lean_Expr_const___override(x_1, x_45);
lean_inc_n(x_37, 3);
x_47 = l_Lean_mkApp3(x_46, x_37, x_37, x_37);
x_48 = lean_box(0);
x_49 = l_Lean_Meta_synthInstance(x_47, x_48, x_5, x_6, x_7, x_8, x_41);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = l_Lean_Expr_const___override(x_2, x_45);
lean_inc_n(x_37, 2);
x_54 = l_Lean_mkApp6(x_53, x_37, x_37, x_37, x_50, x_3, x_4);
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
else
{
lean_dec(x_45);
lean_dec(x_37);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_49;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_ctor_get(x_39, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_58 = x_39;
} else {
 lean_dec_ref(x_39);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_mk_string_unchecked("HAdd", 4, 4);
lean_inc(x_8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("hAdd", 4, 4);
x_11 = l_Lean_Name_mkStr2(x_8, x_10);
x_12 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(x_9, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_mk_string_unchecked("HSub", 4, 4);
lean_inc(x_8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("hSub", 4, 4);
x_11 = l_Lean_Name_mkStr2(x_8, x_10);
x_12 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(x_9, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_mk_string_unchecked("HMul", 4, 4);
lean_inc(x_8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("hMul", 4, 4);
x_11 = l_Lean_Name_mkStr2(x_8, x_10);
x_12 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(x_9, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_10 = lean_infer_type(x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_12);
x_14 = l_Lean_Meta_getDecLevel(x_12, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 1, x_17);
lean_ctor_set(x_10, 0, x_15);
lean_inc(x_10);
x_18 = l_Lean_Expr_const___override(x_1, x_10);
lean_inc(x_12);
x_19 = l_Lean_Expr_app___override(x_18, x_12);
x_20 = lean_box(0);
x_21 = l_Lean_Meta_synthInstance(x_19, x_20, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_Expr_const___override(x_2, x_10);
x_25 = l_Lean_mkApp4(x_24, x_12, x_23, x_3, x_4);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = l_Lean_Expr_const___override(x_2, x_10);
x_29 = l_Lean_mkApp4(x_28, x_12, x_26, x_3, x_4);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
lean_dec(x_10);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_21;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_10);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
return x_14;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_10, 0);
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_35);
x_37 = l_Lean_Meta_getDecLevel(x_35, x_5, x_6, x_7, x_8, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_41);
x_42 = l_Lean_Expr_const___override(x_1, x_41);
lean_inc(x_35);
x_43 = l_Lean_Expr_app___override(x_42, x_35);
x_44 = lean_box(0);
x_45 = l_Lean_Meta_synthInstance(x_43, x_44, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = l_Lean_Expr_const___override(x_2, x_41);
x_50 = l_Lean_mkApp4(x_49, x_35, x_46, x_3, x_4);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_dec(x_41);
lean_dec(x_35);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_45;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_35);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_ctor_get(x_37, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_37, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_54 = x_37;
} else {
 lean_dec_ref(x_37);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_mk_string_unchecked("LE", 2, 2);
lean_inc(x_8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("le", 2, 2);
x_11 = l_Lean_Name_mkStr2(x_8, x_10);
x_12 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(x_9, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_mk_string_unchecked("LT", 2, 2);
lean_inc(x_8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("lt", 2, 2);
x_11 = l_Lean_Name_mkStr2(x_8, x_10);
x_12 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(x_9, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_mk_string_unchecked("propext", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_unsigned_to_nat(3u);
x_10 = l_Lean_Expr_isAppOfArity(x_1, x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_mk_string_unchecked("Iff", 3, 3);
x_12 = lean_mk_string_unchecked("of_eq", 5, 5);
x_13 = l_Lean_Name_mkStr2(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_1);
x_17 = l_Lean_Meta_mkAppM(x_13, x_16, x_2, x_3, x_4, x_5, x_6);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_8430_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_2 = lean_mk_string_unchecked("Meta", 4, 4);
x_3 = lean_mk_string_unchecked("appBuilder", 10, 10);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
lean_inc(x_2);
x_9 = l_Lean_Name_str___override(x_8, x_2);
x_10 = lean_mk_string_unchecked("initFn", 6, 6);
x_11 = l_Lean_Name_str___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("_@", 2, 2);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = l_Lean_Name_str___override(x_13, x_7);
lean_inc(x_2);
x_15 = l_Lean_Name_str___override(x_14, x_2);
x_16 = lean_mk_string_unchecked("AppBuilder", 10, 10);
x_17 = l_Lean_Name_str___override(x_15, x_16);
x_18 = lean_mk_string_unchecked("_hyg", 4, 4);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_unsigned_to_nat(8430u);
x_21 = l_Lean_Name_num___override(x_19, x_20);
x_22 = lean_unbox(x_5);
lean_inc(x_21);
x_23 = l_Lean_registerTraceClass(x_4, x_22, x_21, x_1);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_mk_string_unchecked("result", 6, 6);
lean_inc(x_3);
lean_inc(x_2);
x_26 = l_Lean_Name_mkStr3(x_2, x_3, x_25);
x_27 = lean_box(1);
x_28 = lean_unbox(x_27);
lean_inc(x_21);
x_29 = l_Lean_registerTraceClass(x_26, x_28, x_21, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_mk_string_unchecked("error", 5, 5);
x_32 = l_Lean_Name_mkStr3(x_2, x_3, x_31);
x_33 = lean_unbox(x_27);
x_34 = l_Lean_registerTraceClass(x_32, x_33, x_21, x_30);
return x_34;
}
else
{
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_2);
return x_29;
}
}
else
{
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_2);
return x_23;
}
}
}
lean_object* initialize_Lean_Structure(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_DecLevel(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Structure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DecLevel(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_8430_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
