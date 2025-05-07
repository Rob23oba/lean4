// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Types
// Imports: Lean.Meta.AppBuilder Lean.Meta.CongrTheorems Lean.Meta.Eqns Lean.Meta.Tactic.Replace Lean.Meta.Tactic.Simp.SimpTheorems Lean.Meta.Tactic.Simp.SimpCongrTheorems
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_matcher(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Simp_UsedSimps_toArray_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkImpCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_Simp_mkCongrSimp_x3f_spec__0(lean_object*, size_t, size_t);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Meta_Simp_Result_addLambdas_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedResult;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_congrArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint32_t l_UInt32_ofNatTruncate(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Config_toConfigWithKey(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setMemoize(lean_object*, uint8_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addForalls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Meta_instBEqOrigin___lam__0___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addForalls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_elimDummyEqRec(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedStep;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addLambdas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dandThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withIncDischargeDepth___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setLctxInitIndices___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpMetaConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_getProof_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpIndexConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelMVars_visitExpr_spec__1___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_SimpTheorems_eraseCore_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Meta_Simp_mkCongrSimp_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DStep_addExtraArgs(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withIncDischargeDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMPR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_congrArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Meta_Simp_mkCongrSimp_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Meta_Simp_Result_addForalls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setFailIfUnchanged(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setLctxInitIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqMPR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instAndThenDSimproc;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setFailIfUnchanged___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedUsedSimps;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setZetaDeltaSet___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_Result_addExtraArgs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_removeUnnecessaryCasts_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TransformStep_toStep(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
uint8_t l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_toMethodsRefImpl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_MethodsRefPointed;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Meta_Simp_mkCongrSimp_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___boxed(lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setSimpTheorems___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setLctxInitIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Meta_Simp_mkCongrSimp_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransResultStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withIncDischargeDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isInstImplicit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withIncDischargeDepth___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpIndexConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instHashableOrigin___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setMemoize___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instAndThenDSimproc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpMetaConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedSimprocs;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_toArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_removeUnnecessaryCasts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransOptProofResult(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedStats;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedDiagnostics;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_Result_addExtraArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_Simp_mkCongrSimp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkImpCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpMetaConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Meta_Simp_UsedSimps_toArray_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpIndexConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addExtraArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_applySimpResultToTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_addExtraArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setAutoUnfold___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addLambdas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_removeUnnecessaryCasts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setAutoUnfold(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setSimpTheorems(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry;
lean_object* l_Lean_isDiagnosticsEnabled___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addExtraArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instAndThenSimproc;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedContext;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setZetaDeltaSet(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_addExtraArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instAndThenSimproc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpIndexConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_MethodsRef_toMethodsImpl(lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DStep_addExtraArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_post(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFunExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_MethodsRef_toMethodsImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___Lean_Meta_Simp_UsedSimps_toArray_spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabitedEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_isDeclToUnfold___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setLctxInitIndices___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_num_indices(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Context_isDeclToUnfold(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Meta_Simp_UsedSimps_toArray_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_removeUnnecessaryCasts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_instBEq;
lean_object* lean_array_get_size(lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelMVars_visitExpr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_getCongrSimpKinds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_toMethodsRefImpl___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpMetaConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_insert(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_SMap_switch___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Meta_Simp_Result_addLambdas_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransOptProofResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Simp_UsedSimps_toArray_spec__0___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___Lean_Meta_Simp_UsedSimps_toArray_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Meta_Simp_Result_addForalls_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instHashableName;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0___lam__0___boxed(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedResult() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_Expr_const___override(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_8);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransOptProofResult(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (x_2 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
if (x_2 == 0)
{
lean_dec(x_3);
x_16 = x_2;
goto block_19;
}
else
{
uint8_t x_20; 
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
lean_dec(x_3);
x_16 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = l_Lean_Meta_mkEqTrans(x_21, x_23, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
lean_ctor_set(x_14, 0, x_25);
if (x_2 == 0)
{
lean_dec(x_3);
x_29 = x_2;
goto block_32;
}
else
{
uint8_t x_33; 
x_33 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
lean_dec(x_3);
x_29 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_14);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_29);
if (lean_is_scalar(x_27)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_27;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_14);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
return x_24;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_24, 0);
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_24);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_14, 0);
lean_inc(x_38);
lean_dec(x_14);
x_39 = l_Lean_Meta_mkEqTrans(x_21, x_38, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_40);
if (x_2 == 0)
{
lean_dec(x_3);
x_45 = x_2;
goto block_48;
}
else
{
uint8_t x_49; 
x_49 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
lean_dec(x_3);
x_45 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_45);
if (lean_is_scalar(x_42)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_42;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_3);
x_50 = lean_ctor_get(x_39, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_39, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_52 = x_39;
} else {
 lean_dec_ref(x_39);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransOptProofResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_10 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_8, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqSymm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = l_Lean_Meta_mkEqSymm(x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_8, 0, x_16);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_8);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_17);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
lean_ctor_set(x_8, 0, x_19);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_8);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_free_object(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_8, 0);
lean_inc(x_28);
lean_dec(x_8);
x_29 = l_Lean_Meta_mkEqSymm(x_28, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_35 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_34);
if (lean_is_scalar(x_32)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_32;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_39 = x_29;
} else {
 lean_dec_ref(x_29);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; uint32_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_5);
x_6 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_6);
x_7 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 2, x_7);
x_8 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 3, x_8);
x_9 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 4, x_9);
x_10 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 5, x_10);
x_11 = lean_unbox(x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 6, x_11);
x_12 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 7, x_12);
x_13 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 8, x_13);
x_14 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 9, x_14);
x_15 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 10, x_15);
x_16 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 11, x_16);
x_17 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 12, x_17);
x_18 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 13, x_18);
x_19 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 14, x_19);
x_20 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 15, x_20);
x_21 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 16, x_21);
x_22 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 17, x_22);
x_23 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 18, x_23);
x_24 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 19, x_24);
x_25 = lean_box(0);
x_26 = lean_box(0);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 0, 18);
x_29 = lean_unbox(x_2);
lean_ctor_set_uint8(x_28, 0, x_29);
x_30 = lean_unbox(x_2);
lean_ctor_set_uint8(x_28, 1, x_30);
x_31 = lean_unbox(x_2);
lean_ctor_set_uint8(x_28, 2, x_31);
x_32 = lean_unbox(x_2);
lean_ctor_set_uint8(x_28, 3, x_32);
x_33 = lean_unbox(x_2);
lean_ctor_set_uint8(x_28, 4, x_33);
x_34 = lean_unbox(x_2);
lean_ctor_set_uint8(x_28, 5, x_34);
x_35 = lean_unbox(x_2);
lean_ctor_set_uint8(x_28, 6, x_35);
x_36 = lean_unbox(x_2);
lean_ctor_set_uint8(x_28, 7, x_36);
x_37 = lean_unbox(x_2);
lean_ctor_set_uint8(x_28, 8, x_37);
x_38 = lean_unbox(x_26);
lean_ctor_set_uint8(x_28, 9, x_38);
x_39 = lean_unbox(x_3);
lean_ctor_set_uint8(x_28, 10, x_39);
x_40 = lean_unbox(x_2);
lean_ctor_set_uint8(x_28, 11, x_40);
x_41 = lean_unbox(x_2);
lean_ctor_set_uint8(x_28, 12, x_41);
x_42 = lean_unbox(x_2);
lean_ctor_set_uint8(x_28, 13, x_42);
x_43 = lean_unbox(x_27);
lean_ctor_set_uint8(x_28, 14, x_43);
x_44 = lean_unbox(x_2);
lean_ctor_set_uint8(x_28, 15, x_44);
x_45 = lean_unbox(x_2);
lean_ctor_set_uint8(x_28, 16, x_45);
x_46 = lean_unbox(x_2);
lean_ctor_set_uint8(x_28, 17, x_46);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_uint64_of_nat(x_47);
x_49 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_49, 0, x_28);
lean_ctor_set_uint64(x_49, sizeof(void*)*1, x_48);
x_50 = lean_uint32_of_nat(x_47);
x_51 = l_Array_empty(lean_box(0));
x_52 = lean_box(1);
x_53 = lean_unsigned_to_nat(8u);
x_54 = lean_unsigned_to_nat(2u);
x_55 = lean_nat_shiftl(x_53, x_54);
x_56 = lean_unsigned_to_nat(3u);
x_57 = lean_nat_div(x_55, x_56);
lean_dec(x_55);
x_58 = l_Nat_nextPowerOfTwo(x_57);
lean_dec(x_57);
x_59 = lean_box(0);
x_60 = lean_mk_array(x_58, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_47);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_unbox(x_52);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_65);
x_66 = lean_box(0);
lean_inc(x_49);
x_67 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_67, 0, x_4);
lean_ctor_set(x_67, 1, x_25);
lean_ctor_set(x_67, 2, x_25);
lean_ctor_set(x_67, 3, x_49);
lean_ctor_set(x_67, 4, x_49);
lean_ctor_set(x_67, 5, x_51);
lean_ctor_set(x_67, 6, x_64);
lean_ctor_set(x_67, 7, x_66);
lean_ctor_set(x_67, 8, x_1);
lean_ctor_set_uint32(x_67, sizeof(void*)*9, x_50);
lean_ctor_set_uint32(x_67, sizeof(void*)*9 + 4, x_50);
x_68 = lean_unbox(x_2);
lean_ctor_set_uint8(x_67, sizeof(void*)*9 + 8, x_68);
return x_67;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 10);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_2, x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_mk_string_unchecked("Nat", 3, 3);
x_11 = lean_mk_string_unchecked("Linear", 6, 6);
x_12 = lean_mk_string_unchecked("ExprCnstr", 9, 9);
x_13 = lean_mk_string_unchecked("eq_of_toNormPoly_eq", 19, 19);
x_14 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_13);
x_15 = l_Lean_Environment_contains(x_9, x_14, x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
x_23 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 5);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 6);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 7);
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 8);
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 9);
x_28 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 11);
x_29 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 12);
x_30 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 13);
x_31 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 14);
x_32 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 15);
x_33 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 16);
x_34 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 17);
x_35 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 18);
x_36 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 19);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_37, 0, x_16);
lean_ctor_set(x_37, 1, x_17);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_18);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 1, x_19);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 2, x_20);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 3, x_21);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 4, x_22);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 5, x_23);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 6, x_24);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 7, x_25);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 8, x_26);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 9, x_27);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 10, x_15);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 11, x_28);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 12, x_29);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 13, x_30);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 14, x_31);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 15, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 16, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 17, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 18, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 19, x_36);
lean_ctor_set(x_6, 0, x_37);
return x_6;
}
else
{
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_38 = lean_ctor_get(x_6, 0);
x_39 = lean_ctor_get(x_6, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_6);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_mk_string_unchecked("Nat", 3, 3);
x_42 = lean_mk_string_unchecked("Linear", 6, 6);
x_43 = lean_mk_string_unchecked("ExprCnstr", 9, 9);
x_44 = lean_mk_string_unchecked("eq_of_toNormPoly_eq", 19, 19);
x_45 = l_Lean_Name_mkStr4(x_41, x_42, x_43, x_44);
x_46 = l_Lean_Environment_contains(x_40, x_45, x_4);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_50 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_51 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
x_52 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_53 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
x_54 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 5);
x_55 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 6);
x_56 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 7);
x_57 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 8);
x_58 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 9);
x_59 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 11);
x_60 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 12);
x_61 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 13);
x_62 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 14);
x_63 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 15);
x_64 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 16);
x_65 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 17);
x_66 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 18);
x_67 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 19);
lean_dec(x_1);
x_68 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_68, 0, x_47);
lean_ctor_set(x_68, 1, x_48);
lean_ctor_set_uint8(x_68, sizeof(void*)*2, x_49);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 1, x_50);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 2, x_51);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 3, x_52);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 4, x_53);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 5, x_54);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 6, x_55);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 7, x_56);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 8, x_57);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 9, x_58);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 10, x_46);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 11, x_59);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 12, x_60);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 13, x_61);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 14, x_62);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 15, x_63);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 16, x_64);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 17, x_65);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 18, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 19, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_39);
return x_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_1);
lean_ctor_set(x_70, 1, x_39);
return x_70;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get_uint8(x_9, 0);
x_11 = lean_ctor_get_uint8(x_9, 1);
x_12 = lean_ctor_get_uint8(x_9, 2);
x_13 = lean_ctor_get_uint8(x_9, 3);
x_14 = lean_ctor_get_uint8(x_9, 4);
x_15 = lean_ctor_get_uint8(x_9, 5);
x_16 = lean_ctor_get_uint8(x_9, 6);
x_17 = lean_ctor_get_uint8(x_9, 7);
x_18 = lean_ctor_get_uint8(x_9, 8);
x_19 = lean_box(2);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 6);
x_21 = lean_ctor_get_uint8(x_9, 11);
lean_dec(x_9);
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 7);
x_23 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
x_24 = lean_box(0);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 16);
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 19);
x_28 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_28, 0, x_10);
lean_ctor_set_uint8(x_28, 1, x_11);
lean_ctor_set_uint8(x_28, 2, x_12);
lean_ctor_set_uint8(x_28, 3, x_13);
lean_ctor_set_uint8(x_28, 4, x_14);
lean_ctor_set_uint8(x_28, 5, x_15);
lean_ctor_set_uint8(x_28, 6, x_16);
lean_ctor_set_uint8(x_28, 7, x_17);
lean_ctor_set_uint8(x_28, 8, x_18);
x_29 = lean_unbox(x_19);
lean_ctor_set_uint8(x_28, 9, x_29);
lean_ctor_set_uint8(x_28, 10, x_20);
lean_ctor_set_uint8(x_28, 11, x_21);
lean_ctor_set_uint8(x_28, 12, x_22);
lean_ctor_set_uint8(x_28, 13, x_23);
x_30 = lean_unbox(x_24);
lean_ctor_set_uint8(x_28, 14, x_30);
lean_ctor_set_uint8(x_28, 15, x_25);
lean_ctor_set_uint8(x_28, 16, x_26);
lean_ctor_set_uint8(x_28, 17, x_27);
x_31 = l_Lean_Meta_Config_toConfigWithKey(x_28);
lean_ctor_set(x_7, 0, x_31);
return x_7;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_7);
x_34 = lean_ctor_get_uint8(x_32, 0);
x_35 = lean_ctor_get_uint8(x_32, 1);
x_36 = lean_ctor_get_uint8(x_32, 2);
x_37 = lean_ctor_get_uint8(x_32, 3);
x_38 = lean_ctor_get_uint8(x_32, 4);
x_39 = lean_ctor_get_uint8(x_32, 5);
x_40 = lean_ctor_get_uint8(x_32, 6);
x_41 = lean_ctor_get_uint8(x_32, 7);
x_42 = lean_ctor_get_uint8(x_32, 8);
x_43 = lean_box(2);
x_44 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 6);
x_45 = lean_ctor_get_uint8(x_32, 11);
lean_dec(x_32);
x_46 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 7);
x_47 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
x_48 = lean_box(0);
x_49 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_50 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 16);
x_51 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 19);
x_52 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_52, 0, x_34);
lean_ctor_set_uint8(x_52, 1, x_35);
lean_ctor_set_uint8(x_52, 2, x_36);
lean_ctor_set_uint8(x_52, 3, x_37);
lean_ctor_set_uint8(x_52, 4, x_38);
lean_ctor_set_uint8(x_52, 5, x_39);
lean_ctor_set_uint8(x_52, 6, x_40);
lean_ctor_set_uint8(x_52, 7, x_41);
lean_ctor_set_uint8(x_52, 8, x_42);
x_53 = lean_unbox(x_43);
lean_ctor_set_uint8(x_52, 9, x_53);
lean_ctor_set_uint8(x_52, 10, x_44);
lean_ctor_set_uint8(x_52, 11, x_45);
lean_ctor_set_uint8(x_52, 12, x_46);
lean_ctor_set_uint8(x_52, 13, x_47);
x_54 = lean_unbox(x_48);
lean_ctor_set_uint8(x_52, 14, x_54);
lean_ctor_set_uint8(x_52, 15, x_49);
lean_ctor_set_uint8(x_52, 16, x_50);
lean_ctor_set_uint8(x_52, 17, x_51);
x_55 = l_Lean_Meta_Config_toConfigWithKey(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_33);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_34; 
x_7 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get_uint8(x_8, 0);
x_12 = lean_ctor_get_uint8(x_8, 1);
x_13 = lean_ctor_get_uint8(x_8, 2);
x_14 = lean_ctor_get_uint8(x_8, 3);
x_15 = lean_ctor_get_uint8(x_8, 4);
x_16 = lean_ctor_get_uint8(x_8, 5);
x_17 = lean_ctor_get_uint8(x_8, 6);
x_18 = lean_ctor_get_uint8(x_8, 7);
x_19 = lean_ctor_get_uint8(x_8, 8);
x_20 = lean_box(2);
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 6);
x_22 = lean_ctor_get_uint8(x_8, 11);
lean_dec(x_8);
x_23 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 7);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
x_34 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 8);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_box(0);
x_36 = lean_unbox(x_35);
x_25 = x_36;
goto block_33;
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_box(2);
x_38 = lean_unbox(x_37);
x_25 = x_38;
goto block_33;
}
block_33:
{
uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 16);
x_28 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 19);
x_29 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_29, 0, x_11);
lean_ctor_set_uint8(x_29, 1, x_12);
lean_ctor_set_uint8(x_29, 2, x_13);
lean_ctor_set_uint8(x_29, 3, x_14);
lean_ctor_set_uint8(x_29, 4, x_15);
lean_ctor_set_uint8(x_29, 5, x_16);
lean_ctor_set_uint8(x_29, 6, x_17);
lean_ctor_set_uint8(x_29, 7, x_18);
lean_ctor_set_uint8(x_29, 8, x_19);
x_30 = lean_unbox(x_20);
lean_ctor_set_uint8(x_29, 9, x_30);
lean_ctor_set_uint8(x_29, 10, x_21);
lean_ctor_set_uint8(x_29, 11, x_22);
lean_ctor_set_uint8(x_29, 12, x_23);
lean_ctor_set_uint8(x_29, 13, x_24);
lean_ctor_set_uint8(x_29, 14, x_25);
lean_ctor_set_uint8(x_29, 15, x_26);
lean_ctor_set_uint8(x_29, 16, x_27);
lean_ctor_set_uint8(x_29, 17, x_28);
x_31 = l_Lean_Meta_Config_toConfigWithKey(x_29);
if (lean_is_scalar(x_10)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_10;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_9);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_updateArith___redArg(x_1, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig(x_10, x_4, x_5, x_6, x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig(x_10, x_4, x_5, x_6, x_7, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint32_t x_20; lean_object* x_21; lean_object* x_22; uint32_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_box(0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
x_20 = l_UInt32_ofNatTruncate(x_19);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_uint32_of_nat(x_22);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_13);
lean_ctor_set(x_25, 4, x_17);
lean_ctor_set(x_25, 5, x_2);
lean_ctor_set(x_25, 6, x_3);
lean_ctor_set(x_25, 7, x_21);
lean_ctor_set(x_25, 8, x_22);
lean_ctor_set_uint32(x_25, sizeof(void*)*9, x_20);
lean_ctor_set_uint32(x_25, sizeof(void*)*9 + 4, x_23);
x_26 = lean_unbox(x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*9 + 8, x_26);
lean_ctor_set(x_15, 0, x_25);
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint32_t x_31; lean_object* x_32; lean_object* x_33; uint32_t x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_box(0);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
x_31 = l_UInt32_ofNatTruncate(x_30);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_uint32_of_nat(x_33);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_36, 0, x_10);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_29);
lean_ctor_set(x_36, 3, x_13);
lean_ctor_set(x_36, 4, x_27);
lean_ctor_set(x_36, 5, x_2);
lean_ctor_set(x_36, 6, x_3);
lean_ctor_set(x_36, 7, x_32);
lean_ctor_set(x_36, 8, x_33);
lean_ctor_set_uint32(x_36, sizeof(void*)*9, x_31);
lean_ctor_set_uint32(x_36, sizeof(void*)*9 + 4, x_34);
x_37 = lean_unbox(x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 8, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_28);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_mkContext(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkMetaConfig(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_mkIndexConfig(x_2, x_3, x_4, x_5, x_6, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint32_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get_uint32(x_1, sizeof(void*)*9);
x_17 = lean_ctor_get(x_1, 5);
x_18 = lean_ctor_get(x_1, 6);
x_19 = lean_ctor_get(x_1, 7);
x_20 = lean_ctor_get_uint32(x_1, sizeof(void*)*9 + 4);
x_21 = lean_ctor_get(x_1, 8);
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 8);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
x_23 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_14);
lean_ctor_set(x_23, 2, x_15);
lean_ctor_set(x_23, 3, x_9);
lean_ctor_set(x_23, 4, x_13);
lean_ctor_set(x_23, 5, x_17);
lean_ctor_set(x_23, 6, x_18);
lean_ctor_set(x_23, 7, x_19);
lean_ctor_set(x_23, 8, x_21);
lean_ctor_set_uint32(x_23, sizeof(void*)*9, x_16);
lean_ctor_set_uint32(x_23, sizeof(void*)*9 + 4, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*9 + 8, x_22);
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint32_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint32_t x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_1, 2);
x_28 = lean_ctor_get_uint32(x_1, sizeof(void*)*9);
x_29 = lean_ctor_get(x_1, 5);
x_30 = lean_ctor_get(x_1, 6);
x_31 = lean_ctor_get(x_1, 7);
x_32 = lean_ctor_get_uint32(x_1, sizeof(void*)*9 + 4);
x_33 = lean_ctor_get(x_1, 8);
x_34 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 8);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
x_35 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_26);
lean_ctor_set(x_35, 2, x_27);
lean_ctor_set(x_35, 3, x_9);
lean_ctor_set(x_35, 4, x_24);
lean_ctor_set(x_35, 5, x_29);
lean_ctor_set(x_35, 6, x_30);
lean_ctor_set(x_35, 7, x_31);
lean_ctor_set(x_35, 8, x_33);
lean_ctor_set_uint32(x_35, sizeof(void*)*9, x_28);
lean_ctor_set_uint32(x_35, sizeof(void*)*9 + 4, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*9 + 8, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_25);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Context_setConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setSimpTheorems(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_ctor_get_uint32(x_1, sizeof(void*)*9);
x_9 = lean_ctor_get(x_1, 6);
x_10 = lean_ctor_get(x_1, 7);
x_11 = lean_ctor_get_uint32(x_1, sizeof(void*)*9 + 4);
x_12 = lean_ctor_get(x_1, 8);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 8);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_5);
lean_ctor_set(x_14, 3, x_6);
lean_ctor_set(x_14, 4, x_7);
lean_ctor_set(x_14, 5, x_2);
lean_ctor_set(x_14, 6, x_9);
lean_ctor_set(x_14, 7, x_10);
lean_ctor_set(x_14, 8, x_12);
lean_ctor_set_uint32(x_14, sizeof(void*)*9, x_8);
lean_ctor_set_uint32(x_14, sizeof(void*)*9 + 4, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*9 + 8, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setSimpTheorems___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Context_setSimpTheorems(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setLctxInitIndices___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint32_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint32_t x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_ctor_get(x_1, 4);
x_10 = lean_ctor_get_uint32(x_1, sizeof(void*)*9);
x_11 = lean_ctor_get(x_1, 5);
x_12 = lean_ctor_get(x_1, 6);
x_13 = lean_ctor_get(x_1, 7);
x_14 = lean_ctor_get_uint32(x_1, sizeof(void*)*9 + 4);
x_15 = lean_local_ctx_num_indices(x_4);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 8);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_7);
lean_ctor_set(x_17, 3, x_8);
lean_ctor_set(x_17, 4, x_9);
lean_ctor_set(x_17, 5, x_11);
lean_ctor_set(x_17, 6, x_12);
lean_ctor_set(x_17, 7, x_13);
lean_ctor_set(x_17, 8, x_15);
lean_ctor_set_uint32(x_17, sizeof(void*)*9, x_10);
lean_ctor_set_uint32(x_17, sizeof(void*)*9 + 4, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*9 + 8, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setLctxInitIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Context_setLctxInitIndices___redArg(x_1, x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setLctxInitIndices___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_Context_setLctxInitIndices___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setLctxInitIndices___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Context_setLctxInitIndices(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setAutoUnfold(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint32_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint32_t x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 2);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 3);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 4);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 5);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 6);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 7);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 8);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 9);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 10);
x_16 = lean_box(1);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 12);
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 13);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 14);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 15);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 16);
x_22 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 17);
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 18);
x_24 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 19);
lean_inc(x_4);
lean_inc(x_3);
x_25 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 1, x_6);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 2, x_7);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 3, x_8);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 4, x_9);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 5, x_10);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 6, x_11);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 7, x_12);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 8, x_13);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 9, x_14);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 10, x_15);
x_26 = lean_unbox(x_16);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 11, x_26);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 12, x_17);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 13, x_18);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 14, x_19);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 15, x_20);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 16, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 17, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 18, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 19, x_24);
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_ctor_get(x_1, 2);
x_29 = lean_ctor_get(x_1, 3);
x_30 = lean_ctor_get(x_1, 4);
x_31 = lean_ctor_get_uint32(x_1, sizeof(void*)*9);
x_32 = lean_ctor_get(x_1, 5);
x_33 = lean_ctor_get(x_1, 6);
x_34 = lean_ctor_get(x_1, 7);
x_35 = lean_ctor_get_uint32(x_1, sizeof(void*)*9 + 4);
x_36 = lean_ctor_get(x_1, 8);
x_37 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 8);
lean_inc(x_36);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_38 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_27);
lean_ctor_set(x_38, 2, x_28);
lean_ctor_set(x_38, 3, x_29);
lean_ctor_set(x_38, 4, x_30);
lean_ctor_set(x_38, 5, x_32);
lean_ctor_set(x_38, 6, x_33);
lean_ctor_set(x_38, 7, x_34);
lean_ctor_set(x_38, 8, x_36);
lean_ctor_set_uint32(x_38, sizeof(void*)*9, x_31);
lean_ctor_set_uint32(x_38, sizeof(void*)*9 + 4, x_35);
lean_ctor_set_uint8(x_38, sizeof(void*)*9 + 8, x_37);
return x_38;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setAutoUnfold___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_Context_setAutoUnfold(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setFailIfUnchanged(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint32_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint32_t x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
x_8 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 2);
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 3);
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 4);
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 5);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 6);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 7);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 8);
x_15 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 9);
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 10);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 11);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 12);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 14);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 15);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 16);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 17);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 18);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 19);
lean_inc(x_5);
lean_inc(x_4);
x_25 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_5);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_6);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 1, x_7);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 2, x_8);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 3, x_9);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 4, x_10);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 5, x_11);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 6, x_12);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 7, x_13);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 8, x_14);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 9, x_15);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 10, x_16);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 11, x_17);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 12, x_18);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 13, x_2);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 14, x_19);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 15, x_20);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 16, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 17, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 18, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 19, x_24);
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_1, 2);
x_28 = lean_ctor_get(x_1, 3);
x_29 = lean_ctor_get(x_1, 4);
x_30 = lean_ctor_get_uint32(x_1, sizeof(void*)*9);
x_31 = lean_ctor_get(x_1, 5);
x_32 = lean_ctor_get(x_1, 6);
x_33 = lean_ctor_get(x_1, 7);
x_34 = lean_ctor_get_uint32(x_1, sizeof(void*)*9 + 4);
x_35 = lean_ctor_get(x_1, 8);
x_36 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 8);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
x_37 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_26);
lean_ctor_set(x_37, 2, x_27);
lean_ctor_set(x_37, 3, x_28);
lean_ctor_set(x_37, 4, x_29);
lean_ctor_set(x_37, 5, x_31);
lean_ctor_set(x_37, 6, x_32);
lean_ctor_set(x_37, 7, x_33);
lean_ctor_set(x_37, 8, x_35);
lean_ctor_set_uint32(x_37, sizeof(void*)*9, x_30);
lean_ctor_set_uint32(x_37, sizeof(void*)*9 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*9 + 8, x_36);
return x_37;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setFailIfUnchanged___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Meta_Simp_Context_setFailIfUnchanged(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setMemoize(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint32_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint32_t x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 2);
x_8 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 3);
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 4);
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 5);
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 6);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 7);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 8);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 9);
x_15 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 10);
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 11);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 12);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 13);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 14);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 15);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 16);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 17);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 18);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 19);
lean_inc(x_5);
lean_inc(x_4);
x_25 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_5);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_6);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 1, x_2);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 2, x_7);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 3, x_8);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 4, x_9);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 5, x_10);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 6, x_11);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 7, x_12);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 8, x_13);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 9, x_14);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 10, x_15);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 11, x_16);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 12, x_17);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 13, x_18);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 14, x_19);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 15, x_20);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 16, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 17, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 18, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 19, x_24);
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_1, 2);
x_28 = lean_ctor_get(x_1, 3);
x_29 = lean_ctor_get(x_1, 4);
x_30 = lean_ctor_get_uint32(x_1, sizeof(void*)*9);
x_31 = lean_ctor_get(x_1, 5);
x_32 = lean_ctor_get(x_1, 6);
x_33 = lean_ctor_get(x_1, 7);
x_34 = lean_ctor_get_uint32(x_1, sizeof(void*)*9 + 4);
x_35 = lean_ctor_get(x_1, 8);
x_36 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 8);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
x_37 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_26);
lean_ctor_set(x_37, 2, x_27);
lean_ctor_set(x_37, 3, x_28);
lean_ctor_set(x_37, 4, x_29);
lean_ctor_set(x_37, 5, x_31);
lean_ctor_set(x_37, 6, x_32);
lean_ctor_set(x_37, 7, x_33);
lean_ctor_set(x_37, 8, x_35);
lean_ctor_set_uint32(x_37, sizeof(void*)*9, x_30);
lean_ctor_set_uint32(x_37, sizeof(void*)*9 + 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*9 + 8, x_36);
return x_37;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setMemoize___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Meta_Simp_Context_setMemoize(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setZetaDeltaSet(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_ctor_get_uint32(x_1, sizeof(void*)*9);
x_8 = lean_ctor_get(x_1, 5);
x_9 = lean_ctor_get(x_1, 6);
x_10 = lean_ctor_get(x_1, 7);
x_11 = lean_ctor_get_uint32(x_1, sizeof(void*)*9 + 4);
x_12 = lean_ctor_get(x_1, 8);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 8);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 3, x_5);
lean_ctor_set(x_14, 4, x_6);
lean_ctor_set(x_14, 5, x_8);
lean_ctor_set(x_14, 6, x_9);
lean_ctor_set(x_14, 7, x_10);
lean_ctor_set(x_14, 8, x_12);
lean_ctor_set_uint32(x_14, sizeof(void*)*9, x_7);
lean_ctor_set_uint32(x_14, sizeof(void*)*9 + 4, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*9 + 8, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_setZetaDeltaSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_Context_setZetaDeltaSet(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Context_isDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 5);
x_4 = l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_isDeclToUnfold___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Simp_Context_isDeclToUnfold(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedUsedSimps() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0(lean_box(0), x_3, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_SimpTheorems_eraseCore_spec__1___redArg(x_6, x_2, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_7, x_9);
lean_dec(x_7);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
lean_inc(x_12);
x_13 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_SimpTheorems_eraseCore_spec__1___redArg(x_11, x_2, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_12, x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Simp_UsedSimps_toArray_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_array_push(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_toArray___at___Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg___lam__0), 3, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_instBEqOrigin___lam__0___boxed), 2, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_instHashableOrigin___lam__0___boxed), 1, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_mk_empty_array_with_capacity(x_5);
x_7 = l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl_spec__0(lean_box(0), x_3, x_4, lean_box(0), lean_box(0), x_1, x_2, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___Lean_Meta_Simp_UsedSimps_toArray_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_toArray___at___Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_nat_dec_lt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at___Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg___lam__0___boxed), 2, 0);
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at___Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Meta_Simp_UsedSimps_toArray_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at___Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg(x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_toArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = l_Lean_PersistentHashMap_toArray___at___Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg(x_8);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_10, x_13);
lean_dec(x_10);
x_18 = lean_nat_dec_le(x_11, x_14);
if (x_18 == 0)
{
lean_inc(x_14);
x_15 = x_14;
goto block_17;
}
else
{
x_15 = x_11;
goto block_17;
}
block_17:
{
lean_object* x_16; 
x_16 = l_Array_qsort_sort___at___Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg(x_9, x_15, x_14);
lean_dec(x_14);
x_2 = x_16;
goto block_7;
}
}
else
{
lean_dec(x_10);
x_2 = x_9;
goto block_7;
}
block_7:
{
size_t x_3; lean_object* x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_array_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Meta_Simp_UsedSimps_toArray_spec__0(x_3, x_5, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Simp_UsedSimps_toArray_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Meta_Simp_UsedSimps_toArray_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashMap_toArray___at___Lean_Meta_Simp_UsedSimps_toArray_spec__1___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___Lean_Meta_Simp_UsedSimps_toArray_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_toArray___at___Lean_Meta_Simp_UsedSimps_toArray_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at___Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at___Lean_Meta_Simp_UsedSimps_toArray_spec__2___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Meta_Simp_UsedSimps_toArray_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at___Lean_Meta_Simp_UsedSimps_toArray_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_UsedSimps_toArray___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_UsedSimps_toArray(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedDiagnostics() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_1);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = l_Array_empty(lean_box(0));
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_box(0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_6);
lean_ctor_set_usize(x_9, 4, x_8);
lean_inc(x_2);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set(x_10, 2, x_3);
lean_ctor_set(x_10, 3, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedStats() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_1);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_box(0);
lean_inc(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = l_Array_empty(lean_box(0));
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_3);
lean_ctor_set(x_10, 3, x_3);
lean_ctor_set_usize(x_10, 4, x_9);
lean_inc(x_2);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_5);
lean_ctor_set(x_11, 3, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_MethodsRefPointed() {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withIncDischargeDepth___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; lean_object* x_20; uint32_t x_21; uint32_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get(x_3, 4);
x_15 = lean_ctor_get_uint32(x_3, sizeof(void*)*9);
x_16 = lean_ctor_get(x_3, 5);
x_17 = lean_ctor_get(x_3, 6);
x_18 = lean_ctor_get(x_3, 7);
x_19 = lean_ctor_get_uint32(x_3, sizeof(void*)*9 + 4);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_uint32_of_nat(x_20);
x_22 = lean_uint32_add(x_19, x_21);
x_23 = lean_ctor_get(x_3, 8);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*9 + 8);
lean_inc(x_23);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_25 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_11);
lean_ctor_set(x_25, 2, x_12);
lean_ctor_set(x_25, 3, x_13);
lean_ctor_set(x_25, 4, x_14);
lean_ctor_set(x_25, 5, x_16);
lean_ctor_set(x_25, 6, x_17);
lean_ctor_set(x_25, 7, x_18);
lean_ctor_set(x_25, 8, x_23);
lean_ctor_set_uint32(x_25, sizeof(void*)*9, x_15);
lean_ctor_set_uint32(x_25, sizeof(void*)*9 + 4, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*9 + 8, x_24);
x_26 = lean_apply_8(x_1, x_2, x_25, x_4, x_5, x_6, x_7, x_8, x_9);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withIncDischargeDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint32_t x_20; lean_object* x_21; uint32_t x_22; uint32_t x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
x_15 = lean_ctor_get(x_4, 4);
x_16 = lean_ctor_get_uint32(x_4, sizeof(void*)*9);
x_17 = lean_ctor_get(x_4, 5);
x_18 = lean_ctor_get(x_4, 6);
x_19 = lean_ctor_get(x_4, 7);
x_20 = lean_ctor_get_uint32(x_4, sizeof(void*)*9 + 4);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_uint32_of_nat(x_21);
x_23 = lean_uint32_add(x_20, x_22);
x_24 = lean_ctor_get(x_4, 8);
x_25 = lean_ctor_get_uint8(x_4, sizeof(void*)*9 + 8);
lean_inc(x_24);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_26 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_12);
lean_ctor_set(x_26, 2, x_13);
lean_ctor_set(x_26, 3, x_14);
lean_ctor_set(x_26, 4, x_15);
lean_ctor_set(x_26, 5, x_17);
lean_ctor_set(x_26, 6, x_18);
lean_ctor_set(x_26, 7, x_19);
lean_ctor_set(x_26, 8, x_24);
lean_ctor_set_uint32(x_26, sizeof(void*)*9, x_16);
lean_ctor_set_uint32(x_26, sizeof(void*)*9 + 4, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*9 + 8, x_25);
x_27 = lean_apply_8(x_2, x_3, x_26, x_5, x_6, x_7, x_8, x_9, x_10);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withIncDischargeDepth___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_withIncDischargeDepth___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withIncDischargeDepth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_withIncDischargeDepth(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
x_15 = lean_ctor_get(x_4, 4);
x_16 = lean_ctor_get_uint32(x_4, sizeof(void*)*9);
x_17 = lean_ctor_get(x_4, 6);
x_18 = lean_ctor_get(x_4, 7);
x_19 = lean_ctor_get_uint32(x_4, sizeof(void*)*9 + 4);
x_20 = lean_ctor_get(x_4, 8);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*9 + 8);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_22 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_22, 2, x_13);
lean_ctor_set(x_22, 3, x_14);
lean_ctor_set(x_22, 4, x_15);
lean_ctor_set(x_22, 5, x_1);
lean_ctor_set(x_22, 6, x_17);
lean_ctor_set(x_22, 7, x_18);
lean_ctor_set(x_22, 8, x_20);
lean_ctor_set_uint32(x_22, sizeof(void*)*9, x_16);
lean_ctor_set_uint32(x_22, sizeof(void*)*9 + 4, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*9 + 8, x_21);
x_23 = lean_apply_8(x_2, x_3, x_22, x_5, x_6, x_7, x_8, x_9, x_10);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint32_t x_17; lean_object* x_18; lean_object* x_19; uint32_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
x_17 = lean_ctor_get_uint32(x_5, sizeof(void*)*9);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
x_20 = lean_ctor_get_uint32(x_5, sizeof(void*)*9 + 4);
x_21 = lean_ctor_get(x_5, 8);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 8);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_23 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_13);
lean_ctor_set(x_23, 2, x_14);
lean_ctor_set(x_23, 3, x_15);
lean_ctor_set(x_23, 4, x_16);
lean_ctor_set(x_23, 5, x_2);
lean_ctor_set(x_23, 6, x_18);
lean_ctor_set(x_23, 7, x_19);
lean_ctor_set(x_23, 8, x_21);
lean_ctor_set_uint32(x_23, sizeof(void*)*9, x_17);
lean_ctor_set_uint32(x_23, sizeof(void*)*9 + 4, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*9 + 8, x_22);
x_24 = lean_apply_8(x_3, x_4, x_23, x_6, x_7, x_8, x_9, x_10, x_11);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_withSimpTheorems___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_withSimpTheorems(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get(x_3, 4);
x_15 = lean_ctor_get_uint32(x_3, sizeof(void*)*9);
x_16 = lean_ctor_get(x_3, 5);
x_17 = lean_ctor_get(x_3, 6);
x_18 = lean_ctor_get(x_3, 7);
x_19 = lean_ctor_get_uint32(x_3, sizeof(void*)*9 + 4);
x_20 = lean_ctor_get(x_3, 8);
x_21 = lean_box(1);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_22 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_12);
lean_ctor_set(x_22, 3, x_13);
lean_ctor_set(x_22, 4, x_14);
lean_ctor_set(x_22, 5, x_16);
lean_ctor_set(x_22, 6, x_17);
lean_ctor_set(x_22, 7, x_18);
lean_ctor_set(x_22, 8, x_20);
lean_ctor_set_uint32(x_22, sizeof(void*)*9, x_15);
lean_ctor_set_uint32(x_22, sizeof(void*)*9 + 4, x_19);
x_23 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*9 + 8, x_23);
x_24 = lean_apply_8(x_1, x_2, x_22, x_4, x_5, x_6, x_7, x_8, x_9);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint32_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
x_15 = lean_ctor_get(x_4, 4);
x_16 = lean_ctor_get_uint32(x_4, sizeof(void*)*9);
x_17 = lean_ctor_get(x_4, 5);
x_18 = lean_ctor_get(x_4, 6);
x_19 = lean_ctor_get(x_4, 7);
x_20 = lean_ctor_get_uint32(x_4, sizeof(void*)*9 + 4);
x_21 = lean_ctor_get(x_4, 8);
x_22 = lean_box(1);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_23 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_12);
lean_ctor_set(x_23, 2, x_13);
lean_ctor_set(x_23, 3, x_14);
lean_ctor_set(x_23, 4, x_15);
lean_ctor_set(x_23, 5, x_17);
lean_ctor_set(x_23, 6, x_18);
lean_ctor_set(x_23, 7, x_19);
lean_ctor_set(x_23, 8, x_21);
lean_ctor_set_uint32(x_23, sizeof(void*)*9, x_16);
lean_ctor_set_uint32(x_23, sizeof(void*)*9 + 4, x_20);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*9 + 8, x_24);
x_25 = lean_apply_8(x_2, x_3, x_23, x_5, x_6, x_7, x_8, x_9, x_10);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimp___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_withInDSimp___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withInDSimp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_withInDSimp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpIndexConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_10 = lean_ctor_get(x_3, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_10, sizeof(void*)*1);
lean_dec(x_10);
x_13 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 8);
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 2);
x_16 = lean_ctor_get(x_5, 3);
x_17 = lean_ctor_get(x_5, 4);
x_18 = lean_ctor_get(x_5, 5);
x_19 = lean_ctor_get(x_5, 6);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_22 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_22, 2, x_15);
lean_ctor_set(x_22, 3, x_16);
lean_ctor_set(x_22, 4, x_17);
lean_ctor_set(x_22, 5, x_18);
lean_ctor_set(x_22, 6, x_19);
lean_ctor_set_uint64(x_22, sizeof(void*)*7, x_12);
lean_ctor_set_uint8(x_22, sizeof(void*)*7 + 8, x_13);
lean_ctor_set_uint8(x_22, sizeof(void*)*7 + 9, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*7 + 10, x_21);
x_23 = lean_apply_8(x_1, x_2, x_3, x_4, x_22, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpIndexConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint64_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_11 = lean_ctor_get(x_4, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_11, sizeof(void*)*1);
lean_dec(x_11);
x_14 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_6, 2);
x_17 = lean_ctor_get(x_6, 3);
x_18 = lean_ctor_get(x_6, 4);
x_19 = lean_ctor_get(x_6, 5);
x_20 = lean_ctor_get(x_6, 6);
x_21 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_22 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_23 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_17);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set_uint64(x_23, sizeof(void*)*7, x_13);
lean_ctor_set_uint8(x_23, sizeof(void*)*7 + 8, x_14);
lean_ctor_set_uint8(x_23, sizeof(void*)*7 + 9, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*7 + 10, x_22);
x_24 = lean_apply_8(x_2, x_3, x_4, x_5, x_23, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpIndexConfig___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_withSimpIndexConfig___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpIndexConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_withSimpIndexConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpMetaConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_10 = lean_ctor_get(x_3, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_10, sizeof(void*)*1);
lean_dec(x_10);
x_13 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 8);
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 2);
x_16 = lean_ctor_get(x_5, 3);
x_17 = lean_ctor_get(x_5, 4);
x_18 = lean_ctor_get(x_5, 5);
x_19 = lean_ctor_get(x_5, 6);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_22 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_22, 2, x_15);
lean_ctor_set(x_22, 3, x_16);
lean_ctor_set(x_22, 4, x_17);
lean_ctor_set(x_22, 5, x_18);
lean_ctor_set(x_22, 6, x_19);
lean_ctor_set_uint64(x_22, sizeof(void*)*7, x_12);
lean_ctor_set_uint8(x_22, sizeof(void*)*7 + 8, x_13);
lean_ctor_set_uint8(x_22, sizeof(void*)*7 + 9, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*7 + 10, x_21);
x_23 = lean_apply_8(x_1, x_2, x_3, x_4, x_22, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpMetaConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint64_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_11 = lean_ctor_get(x_4, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_11, sizeof(void*)*1);
lean_dec(x_11);
x_14 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_6, 2);
x_17 = lean_ctor_get(x_6, 3);
x_18 = lean_ctor_get(x_6, 4);
x_19 = lean_ctor_get(x_6, 5);
x_20 = lean_ctor_get(x_6, 6);
x_21 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_22 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_23 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_17);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set_uint64(x_23, sizeof(void*)*7, x_13);
lean_ctor_set_uint8(x_23, sizeof(void*)*7 + 8, x_14);
lean_ctor_set_uint8(x_23, sizeof(void*)*7 + 9, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*7 + 10, x_22);
x_24 = lean_apply_8(x_2, x_3, x_4, x_5, x_23, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpMetaConfig___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_withSimpMetaConfig___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpMetaConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_withSimpMetaConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_simp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_dsimp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_isDiagnosticsEnabled___redArg(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_st_ref_take(x_2, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_16, 4);
x_20 = lean_apply_1(x_1, x_19);
lean_ctor_set(x_16, 4, x_20);
x_21 = lean_st_ref_set(x_2, x_16, x_17);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
x_30 = lean_ctor_get(x_16, 2);
x_31 = lean_ctor_get(x_16, 3);
x_32 = lean_ctor_get(x_16, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_33 = lean_apply_1(x_1, x_32);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_29);
lean_ctor_set(x_34, 2, x_30);
lean_ctor_set(x_34, 3, x_31);
lean_ctor_set(x_34, 4, x_33);
x_35 = lean_st_ref_set(x_2, x_34, x_17);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = lean_box(0);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_isDiagnosticsEnabled___redArg(x_7, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_st_ref_take(x_4, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_21, 4);
x_25 = lean_apply_1(x_1, x_24);
lean_ctor_set(x_21, 4, x_25);
x_26 = lean_st_ref_set(x_4, x_21, x_22);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 1);
x_35 = lean_ctor_get(x_21, 2);
x_36 = lean_ctor_get(x_21, 3);
x_37 = lean_ctor_get(x_21, 4);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_21);
x_38 = lean_apply_1(x_1, x_37);
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_34);
lean_ctor_set(x_39, 2, x_35);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set(x_39, 4, x_38);
x_40 = lean_st_ref_set(x_4, x_39, x_22);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = lean_box(0);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_modifyDiag___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_modifyDiag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_modifyDiag(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedStep() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_Expr_const___override(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_8);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_TransformStep_toStep(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_box(0);
x_5 = lean_box(1);
x_6 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_12);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
}
case 1:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_box(0);
x_17 = lean_box(1);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_unbox(x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_19);
lean_ctor_set(x_1, 0, x_18);
return x_1;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_24);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
return x_25;
}
}
default: 
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_1);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_box(0);
lean_ctor_set(x_1, 0, x_28);
return x_1;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_box(0);
x_32 = lean_box(1);
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_34);
lean_ctor_set(x_27, 0, x_33);
return x_1;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec(x_27);
x_36 = lean_box(0);
x_37 = lean_box(1);
x_38 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_unbox(x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_39);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_1, 0, x_40);
return x_1;
}
}
}
else
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
lean_dec(x_1);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_45 = x_41;
} else {
 lean_dec_ref(x_41);
 x_45 = lean_box(0);
}
x_46 = lean_box(0);
x_47 = lean_box(1);
x_48 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_49);
if (lean_is_scalar(x_45)) {
 x_50 = lean_alloc_ctor(1, 1, 0);
} else {
 x_50 = x_45;
}
lean_ctor_set(x_50, 0, x_48);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTransResultStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_12 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_10, x_11, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_2, 0, x_14);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_2, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_free_object(x_2);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_25 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_23, x_24, x_22, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_33 = x_25;
} else {
 lean_dec_ref(x_25);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
case 1:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_2);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_39 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_37, x_38, x_36, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_ctor_set(x_2, 0, x_41);
lean_ctor_set(x_39, 0, x_2);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_39);
lean_ctor_set(x_2, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_free_object(x_2);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
return x_39;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_39, 0);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_39);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_2, 0);
lean_inc(x_49);
lean_dec(x_2);
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_52 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_50, x_51, x_49, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_53);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_52, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_60 = x_52;
} else {
 lean_dec_ref(x_52);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
default: 
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_2);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_2, 0, x_64);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_2);
lean_ctor_set(x_65, 1, x_7);
return x_65;
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_63);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_63, 0);
x_68 = lean_ctor_get(x_1, 1);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_70 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_68, x_69, x_67, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 0);
lean_ctor_set(x_63, 0, x_72);
lean_ctor_set(x_70, 0, x_2);
return x_70;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_70, 0);
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_70);
lean_ctor_set(x_63, 0, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_2);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_free_object(x_63);
lean_free_object(x_2);
x_76 = !lean_is_exclusive(x_70);
if (x_76 == 0)
{
return x_70;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_70, 0);
x_78 = lean_ctor_get(x_70, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_70);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_63, 0);
lean_inc(x_80);
lean_dec(x_63);
x_81 = lean_ctor_get(x_1, 1);
lean_inc(x_81);
x_82 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_83 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_81, x_82, x_80, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_2, 0, x_87);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_2);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_free_object(x_2);
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_91 = x_83;
} else {
 lean_dec_ref(x_83);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
}
else
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_2, 0);
lean_inc(x_93);
lean_dec(x_2);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_1);
x_95 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_7);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_93, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_98 = x_93;
} else {
 lean_dec_ref(x_93);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_1, 1);
lean_inc(x_99);
x_100 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_101 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_99, x_100, x_97, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_105 = lean_alloc_ctor(1, 1, 0);
} else {
 x_105 = x_98;
}
lean_ctor_set(x_105, 0, x_102);
x_106 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_106, 0, x_105);
if (lean_is_scalar(x_104)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_104;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_103);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_98);
x_108 = lean_ctor_get(x_101, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_101, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_110 = x_101;
} else {
 lean_dec_ref(x_101);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_andThen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 2)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_20 = lean_apply_9(x_2, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_Simp_mkEqTransResultStep(x_18, x_21, x_7, x_8, x_9, x_10, x_22);
return x_23;
}
else
{
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_20;
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instAndThenSimproc___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 2)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_17; 
x_17 = lean_apply_10(x_2, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_20 = lean_apply_10(x_2, x_16, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_Simp_mkEqTransResultStep(x_18, x_21, x_7, x_8, x_9, x_10, x_22);
return x_23;
}
else
{
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_20;
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_instAndThenSimproc() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_instAndThenSimproc___lam__0), 11, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dandThen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 2)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_apply_9(x_2, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
return x_19;
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instAndThenDSimproc___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 2)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_17; 
x_17 = lean_apply_10(x_2, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_apply_10(x_2, x_16, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_19;
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_instAndThenDSimproc() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_instAndThenDSimproc___lam__0), 11, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Array_empty(lean_box(0));
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_5);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocs() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Name_instBEq;
x_2 = l_Lean_instHashableName;
x_3 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), x_1, x_2);
lean_inc(x_5);
lean_inc(x_4);
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_box(0);
x_13 = l_Lean_Expr_const___override(x_11, x_12);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_17);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_box(0);
x_13 = l_Lean_Expr_const___override(x_11, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedMethods() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_instInhabitedMethods___lam__0___boxed), 9, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_instInhabitedMethods___lam__1___boxed), 9, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_instInhabitedMethods___lam__2___boxed), 9, 0);
x_4 = lean_box(0);
lean_inc(x_2);
lean_inc(x_1);
x_5 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set(x_5, 4, x_3);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*5, x_6);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_instInhabitedMethods___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_instInhabitedMethods___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_instInhabitedMethods___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_toMethodsRefImpl(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_toMethodsRefImpl___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_Methods_toMethodsRefImpl(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_MethodsRef_toMethodsImpl(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_MethodsRef_toMethodsImpl___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_MethodsRef_toMethodsImpl(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getMethods___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_getMethods(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_pre(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_apply_9(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_post(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_apply_9(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_getContext(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_getConfig___redArg(x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_getConfig___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_getConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint32_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
x_15 = lean_ctor_get(x_4, 4);
x_16 = lean_ctor_get_uint32(x_4, sizeof(void*)*9);
x_17 = lean_ctor_get(x_4, 5);
x_18 = lean_ctor_get(x_4, 6);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_1);
x_20 = lean_ctor_get_uint32(x_4, sizeof(void*)*9 + 4);
x_21 = lean_ctor_get(x_4, 8);
x_22 = lean_ctor_get_uint8(x_4, sizeof(void*)*9 + 8);
lean_inc(x_21);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_23 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_12);
lean_ctor_set(x_23, 2, x_13);
lean_ctor_set(x_23, 3, x_14);
lean_ctor_set(x_23, 4, x_15);
lean_ctor_set(x_23, 5, x_17);
lean_ctor_set(x_23, 6, x_18);
lean_ctor_set(x_23, 7, x_19);
lean_ctor_set(x_23, 8, x_21);
lean_ctor_set_uint32(x_23, sizeof(void*)*9, x_16);
lean_ctor_set_uint32(x_23, sizeof(void*)*9 + 4, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*9 + 8, x_22);
x_24 = lean_apply_8(x_2, x_3, x_23, x_5, x_6, x_7, x_8, x_9, x_10);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint32_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint32_t x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
x_17 = lean_ctor_get_uint32(x_5, sizeof(void*)*9);
x_18 = lean_ctor_get(x_5, 5);
x_19 = lean_ctor_get(x_5, 6);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_2);
x_21 = lean_ctor_get_uint32(x_5, sizeof(void*)*9 + 4);
x_22 = lean_ctor_get(x_5, 8);
x_23 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 8);
lean_inc(x_22);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_24 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_13);
lean_ctor_set(x_24, 2, x_14);
lean_ctor_set(x_24, 3, x_15);
lean_ctor_set(x_24, 4, x_16);
lean_ctor_set(x_24, 5, x_18);
lean_ctor_set(x_24, 6, x_19);
lean_ctor_set(x_24, 7, x_20);
lean_ctor_set(x_24, 8, x_22);
lean_ctor_set_uint32(x_24, sizeof(void*)*9, x_17);
lean_ctor_set_uint32(x_24, sizeof(void*)*9 + 4, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*9 + 8, x_23);
x_25 = lean_apply_8(x_3, x_4, x_24, x_6, x_7, x_8, x_9, x_10, x_11);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_withParent___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_withParent(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 5);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_getSimpTheorems___redArg(x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_getSimpTheorems___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_getSimpTheorems(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 6);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_getSimpCongrTheorems___redArg(x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_getSimpCongrTheorems___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_getSimpCongrTheorems(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 8);
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_inDSimp___redArg(x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_inDSimp___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_inDSimp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_inDSimp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_6 = lean_st_ref_take(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_2);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 4);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_14);
lean_ctor_set(x_16, 4, x_15);
x_17 = lean_st_ref_set(x_1, x_16, x_8);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_4, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = l_Lean_SMap_switch___redArg(x_19);
lean_dec(x_19);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_17, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_17, 4);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set(x_25, 4, x_24);
x_26 = lean_st_ref_set(x_4, x_25, x_18);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_11, 0);
lean_inc(x_28);
lean_dec(x_11);
x_29 = lean_ctor_get(x_14, 0);
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get_uint8(x_29, sizeof(void*)*2);
lean_dec(x_29);
lean_inc(x_4);
x_32 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_33);
x_36 = l_Lean_Meta_Simp_withPreservedCache___redArg___lam__0(x_4, x_31, x_30, x_35, x_34);
lean_dec(x_35);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_33);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_box(0);
x_44 = l_Lean_Meta_Simp_withPreservedCache___redArg___lam__0(x_4, x_31, x_30, x_43, x_42);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set_tag(x_44, 1);
lean_ctor_set(x_44, 0, x_41);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_11 = lean_st_ref_get(x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_5, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_take(x_5, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = l_Lean_SMap_switch___redArg(x_20);
lean_dec(x_20);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_18, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_18, 4);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_24);
lean_ctor_set(x_26, 4, x_25);
x_27 = lean_st_ref_set(x_5, x_26, x_19);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_12, 0);
lean_inc(x_29);
lean_dec(x_12);
x_30 = lean_ctor_get(x_15, 0);
lean_inc(x_30);
lean_dec(x_15);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get_uint8(x_30, sizeof(void*)*2);
lean_dec(x_30);
lean_inc(x_5);
x_33 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_34);
x_37 = l_Lean_Meta_Simp_withPreservedCache___redArg___lam__0(x_5, x_32, x_31, x_36, x_35);
lean_dec(x_36);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_34);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_dec(x_33);
x_44 = lean_box(0);
x_45 = l_Lean_Meta_Simp_withPreservedCache___redArg___lam__0(x_5, x_32, x_31, x_44, x_43);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 0, x_42);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withPreservedCache___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Meta_Simp_withPreservedCache___redArg___lam__0(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 4);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_10);
lean_ctor_set(x_12, 4, x_11);
x_13 = lean_st_ref_set(x_1, x_12, x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_take(x_4, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_box(1);
x_18 = lean_unsigned_to_nat(8u);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_unsigned_to_nat(2u);
x_21 = lean_nat_shiftl(x_18, x_20);
x_22 = lean_unsigned_to_nat(3u);
x_23 = lean_nat_div(x_21, x_22);
lean_dec(x_21);
x_24 = l_Nat_nextPowerOfTwo(x_23);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = lean_mk_array(x_24, x_25);
lean_ctor_set(x_13, 1, x_26);
lean_ctor_set(x_13, 0, x_19);
x_27 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_unbox(x_17);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_30);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_15, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_15, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_15, 4);
lean_inc(x_34);
lean_dec(x_15);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_32);
lean_ctor_set(x_35, 3, x_33);
lean_ctor_set(x_35, 4, x_34);
x_36 = lean_st_ref_set(x_4, x_35, x_16);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_11, 0);
lean_inc(x_38);
lean_dec(x_11);
lean_inc(x_4);
x_39 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_40);
x_43 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_4, x_38, x_42, x_41);
lean_dec(x_42);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_40);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_39, 1);
lean_inc(x_49);
lean_dec(x_39);
x_50 = lean_box(0);
x_51 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_4, x_38, x_50, x_49);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_48);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_56 = lean_ctor_get(x_13, 0);
x_57 = lean_ctor_get(x_13, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_13);
x_58 = lean_box(1);
x_59 = lean_unsigned_to_nat(8u);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_unsigned_to_nat(2u);
x_62 = lean_nat_shiftl(x_59, x_61);
x_63 = lean_unsigned_to_nat(3u);
x_64 = lean_nat_div(x_62, x_63);
lean_dec(x_62);
x_65 = l_Nat_nextPowerOfTwo(x_64);
lean_dec(x_64);
x_66 = lean_box(0);
x_67 = lean_mk_array(x_65, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_60);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_unbox(x_58);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_72);
x_73 = lean_ctor_get(x_56, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_56, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_56, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_56, 4);
lean_inc(x_76);
lean_dec(x_56);
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_74);
lean_ctor_set(x_77, 3, x_75);
lean_ctor_set(x_77, 4, x_76);
x_78 = lean_st_ref_set(x_4, x_77, x_57);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_ctor_get(x_11, 0);
lean_inc(x_80);
lean_dec(x_11);
lean_inc(x_4);
x_81 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_82);
x_85 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_4, x_80, x_84, x_83);
lean_dec(x_84);
lean_dec(x_4);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_81, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_81, 1);
lean_inc(x_90);
lean_dec(x_81);
x_91 = lean_box(0);
x_92 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_4, x_80, x_91, x_90);
lean_dec(x_4);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
 lean_ctor_set_tag(x_95, 1);
}
lean_ctor_set(x_95, 0, x_89);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_st_ref_get(x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_5, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_box(1);
x_19 = lean_unsigned_to_nat(8u);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_shiftl(x_19, x_21);
x_23 = lean_unsigned_to_nat(3u);
x_24 = lean_nat_div(x_22, x_23);
lean_dec(x_22);
x_25 = l_Nat_nextPowerOfTwo(x_24);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = lean_mk_array(x_25, x_26);
lean_ctor_set(x_14, 1, x_27);
lean_ctor_set(x_14, 0, x_20);
x_28 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_14);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_unbox(x_18);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_31);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_16, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_16, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_16, 4);
lean_inc(x_35);
lean_dec(x_16);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_34);
lean_ctor_set(x_36, 4, x_35);
x_37 = lean_st_ref_set(x_5, x_36, x_17);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_12, 0);
lean_inc(x_39);
lean_dec(x_12);
lean_inc(x_5);
x_40 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_41);
x_44 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_5, x_39, x_43, x_42);
lean_dec(x_43);
lean_dec(x_5);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set(x_44, 0, x_41);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_dec(x_40);
x_51 = lean_box(0);
x_52 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_5, x_39, x_51, x_50);
lean_dec(x_5);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set_tag(x_52, 1);
lean_ctor_set(x_52, 0, x_49);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_57 = lean_ctor_get(x_14, 0);
x_58 = lean_ctor_get(x_14, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_14);
x_59 = lean_box(1);
x_60 = lean_unsigned_to_nat(8u);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_unsigned_to_nat(2u);
x_63 = lean_nat_shiftl(x_60, x_62);
x_64 = lean_unsigned_to_nat(3u);
x_65 = lean_nat_div(x_63, x_64);
lean_dec(x_63);
x_66 = l_Nat_nextPowerOfTwo(x_65);
lean_dec(x_65);
x_67 = lean_box(0);
x_68 = lean_mk_array(x_66, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_unbox(x_59);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_73);
x_74 = lean_ctor_get(x_57, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_57, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_57, 3);
lean_inc(x_76);
x_77 = lean_ctor_get(x_57, 4);
lean_inc(x_77);
lean_dec(x_57);
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_74);
lean_ctor_set(x_78, 2, x_75);
lean_ctor_set(x_78, 3, x_76);
lean_ctor_set(x_78, 4, x_77);
x_79 = lean_st_ref_set(x_5, x_78, x_58);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_ctor_get(x_12, 0);
lean_inc(x_81);
lean_dec(x_12);
lean_inc(x_5);
x_82 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_80);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_83);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_83);
x_86 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_5, x_81, x_85, x_84);
lean_dec(x_85);
lean_dec(x_5);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_ctor_get(x_82, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_82, 1);
lean_inc(x_91);
lean_dec(x_82);
x_92 = lean_box(0);
x_93 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_5, x_81, x_92, x_91);
lean_dec(x_5);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
 lean_ctor_set_tag(x_96, 1);
}
lean_ctor_set(x_96, 0, x_90);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withFreshCache___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_st_ref_get(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_6, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_box(1);
x_20 = lean_unsigned_to_nat(8u);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_nat_shiftl(x_20, x_22);
x_24 = lean_unsigned_to_nat(3u);
x_25 = lean_nat_div(x_23, x_24);
lean_dec(x_23);
x_26 = l_Nat_nextPowerOfTwo(x_25);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = lean_mk_array(x_26, x_27);
lean_ctor_set(x_15, 1, x_28);
lean_ctor_set(x_15, 0, x_21);
x_29 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_unbox(x_19);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_32);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_17, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_17, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_17, 4);
lean_inc(x_36);
lean_dec(x_17);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_34);
lean_ctor_set(x_37, 3, x_35);
lean_ctor_set(x_37, 4, x_36);
x_38 = lean_st_ref_set(x_6, x_37, x_18);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_13, 0);
lean_inc(x_40);
lean_dec(x_13);
x_41 = lean_ctor_get(x_4, 0);
x_42 = lean_ctor_get(x_4, 1);
x_43 = lean_ctor_get(x_4, 2);
x_44 = lean_ctor_get(x_4, 3);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
x_45 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_42);
lean_ctor_set(x_45, 2, x_43);
lean_ctor_set(x_45, 3, x_44);
lean_ctor_set(x_45, 4, x_1);
lean_ctor_set_uint8(x_45, sizeof(void*)*5, x_2);
lean_inc(x_6);
x_46 = lean_apply_8(x_3, x_45, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_47);
x_50 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_6, x_40, x_49, x_48);
lean_dec(x_49);
lean_dec(x_6);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_47);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_46, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_46, 1);
lean_inc(x_56);
lean_dec(x_46);
x_57 = lean_box(0);
x_58 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_6, x_40, x_57, x_56);
lean_dec(x_6);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
lean_ctor_set_tag(x_58, 1);
lean_ctor_set(x_58, 0, x_55);
return x_58;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_55);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_63 = lean_ctor_get(x_15, 0);
x_64 = lean_ctor_get(x_15, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_15);
x_65 = lean_box(1);
x_66 = lean_unsigned_to_nat(8u);
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_unsigned_to_nat(2u);
x_69 = lean_nat_shiftl(x_66, x_68);
x_70 = lean_unsigned_to_nat(3u);
x_71 = lean_nat_div(x_69, x_70);
lean_dec(x_69);
x_72 = l_Nat_nextPowerOfTwo(x_71);
lean_dec(x_71);
x_73 = lean_box(0);
x_74 = lean_mk_array(x_72, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_unbox(x_65);
lean_ctor_set_uint8(x_78, sizeof(void*)*2, x_79);
x_80 = lean_ctor_get(x_63, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_63, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_63, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_63, 4);
lean_inc(x_83);
lean_dec(x_63);
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_80);
lean_ctor_set(x_84, 2, x_81);
lean_ctor_set(x_84, 3, x_82);
lean_ctor_set(x_84, 4, x_83);
x_85 = lean_st_ref_set(x_6, x_84, x_64);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_ctor_get(x_13, 0);
lean_inc(x_87);
lean_dec(x_13);
x_88 = lean_ctor_get(x_4, 0);
x_89 = lean_ctor_get(x_4, 1);
x_90 = lean_ctor_get(x_4, 2);
x_91 = lean_ctor_get(x_4, 3);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
x_92 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set(x_92, 1, x_89);
lean_ctor_set(x_92, 2, x_90);
lean_ctor_set(x_92, 3, x_91);
lean_ctor_set(x_92, 4, x_1);
lean_ctor_set_uint8(x_92, sizeof(void*)*5, x_2);
lean_inc(x_6);
x_93 = lean_apply_8(x_3, x_92, x_5, x_6, x_7, x_8, x_9, x_10, x_86);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_94);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_94);
x_97 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_6, x_87, x_96, x_95);
lean_dec(x_96);
lean_dec(x_6);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_94);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_101 = lean_ctor_get(x_93, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_93, 1);
lean_inc(x_102);
lean_dec(x_93);
x_103 = lean_box(0);
x_104 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_6, x_87, x_103, x_102);
lean_dec(x_6);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
 lean_ctor_set_tag(x_107, 1);
}
lean_ctor_set(x_107, 0, x_101);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_st_ref_get(x_7, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_7, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_box(1);
x_21 = lean_unsigned_to_nat(8u);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_unsigned_to_nat(2u);
x_24 = lean_nat_shiftl(x_21, x_23);
x_25 = lean_unsigned_to_nat(3u);
x_26 = lean_nat_div(x_24, x_25);
lean_dec(x_24);
x_27 = l_Nat_nextPowerOfTwo(x_26);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = lean_mk_array(x_27, x_28);
lean_ctor_set(x_16, 1, x_29);
lean_ctor_set(x_16, 0, x_22);
x_30 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_unbox(x_20);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_33);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_18, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_18, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_18, 4);
lean_inc(x_37);
lean_dec(x_18);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 4, x_37);
x_39 = lean_st_ref_set(x_7, x_38, x_19);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_14, 0);
lean_inc(x_41);
lean_dec(x_14);
x_42 = lean_ctor_get(x_5, 0);
x_43 = lean_ctor_get(x_5, 1);
x_44 = lean_ctor_get(x_5, 2);
x_45 = lean_ctor_get(x_5, 3);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
x_46 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_44);
lean_ctor_set(x_46, 3, x_45);
lean_ctor_set(x_46, 4, x_2);
lean_ctor_set_uint8(x_46, sizeof(void*)*5, x_3);
lean_inc(x_7);
x_47 = lean_apply_8(x_4, x_46, x_6, x_7, x_8, x_9, x_10, x_11, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_48);
x_51 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_7, x_41, x_50, x_49);
lean_dec(x_50);
lean_dec(x_7);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set(x_51, 0, x_48);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_47, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_47, 1);
lean_inc(x_57);
lean_dec(x_47);
x_58 = lean_box(0);
x_59 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_7, x_41, x_58, x_57);
lean_dec(x_7);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
lean_ctor_set_tag(x_59, 1);
lean_ctor_set(x_59, 0, x_56);
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_64 = lean_ctor_get(x_16, 0);
x_65 = lean_ctor_get(x_16, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_16);
x_66 = lean_box(1);
x_67 = lean_unsigned_to_nat(8u);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_unsigned_to_nat(2u);
x_70 = lean_nat_shiftl(x_67, x_69);
x_71 = lean_unsigned_to_nat(3u);
x_72 = lean_nat_div(x_70, x_71);
lean_dec(x_70);
x_73 = l_Nat_nextPowerOfTwo(x_72);
lean_dec(x_72);
x_74 = lean_box(0);
x_75 = lean_mk_array(x_73, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_68);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_unbox(x_66);
lean_ctor_set_uint8(x_79, sizeof(void*)*2, x_80);
x_81 = lean_ctor_get(x_64, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_64, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_64, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_64, 4);
lean_inc(x_84);
lean_dec(x_64);
x_85 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_85, 0, x_79);
lean_ctor_set(x_85, 1, x_81);
lean_ctor_set(x_85, 2, x_82);
lean_ctor_set(x_85, 3, x_83);
lean_ctor_set(x_85, 4, x_84);
x_86 = lean_st_ref_set(x_7, x_85, x_65);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_ctor_get(x_14, 0);
lean_inc(x_88);
lean_dec(x_14);
x_89 = lean_ctor_get(x_5, 0);
x_90 = lean_ctor_get(x_5, 1);
x_91 = lean_ctor_get(x_5, 2);
x_92 = lean_ctor_get(x_5, 3);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
x_93 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_90);
lean_ctor_set(x_93, 2, x_91);
lean_ctor_set(x_93, 3, x_92);
lean_ctor_set(x_93, 4, x_2);
lean_ctor_set_uint8(x_93, sizeof(void*)*5, x_3);
lean_inc(x_7);
x_94 = lean_apply_8(x_4, x_93, x_6, x_7, x_8, x_9, x_10, x_11, x_87);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
lean_inc(x_95);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_95);
x_98 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_7, x_88, x_97, x_96);
lean_dec(x_97);
lean_dec(x_7);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_95);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_ctor_get(x_94, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_94, 1);
lean_inc(x_103);
lean_dec(x_94);
x_104 = lean_box(0);
x_105 = l_Lean_Meta_Simp_withFreshCache___redArg___lam__0(x_7, x_88, x_104, x_103);
lean_dec(x_7);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_107 = x_105;
} else {
 lean_dec_ref(x_105);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
 lean_ctor_set_tag(x_108, 1);
}
lean_ctor_set(x_108, 0, x_102);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_Simp_withDischarger___redArg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withDischarger___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Meta_Simp_withDischarger(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_9; lean_object* x_13; lean_object* x_14; lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_1);
x_18 = lean_nat_dec_lt(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_3);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fget(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_4, 0);
x_25 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 1);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_20, sizeof(void*)*1 + 1);
lean_dec(x_20);
x_28 = lean_name_eq(x_24, x_26);
lean_dec(x_26);
if (x_28 == 0)
{
x_9 = x_28;
goto block_12;
}
else
{
if (x_25 == 0)
{
if (x_27 == 0)
{
x_9 = x_28;
goto block_12;
}
else
{
goto block_8;
}
}
else
{
x_9 = x_27;
goto block_12;
}
}
}
else
{
lean_dec(x_20);
goto block_8;
}
}
else
{
if (lean_obj_tag(x_20) == 0)
{
lean_dec(x_20);
goto block_8;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_4, 0);
x_21 = x_29;
goto block_23;
}
}
block_23:
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_13 = x_21;
x_14 = x_22;
goto block_16;
}
}
block_8:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_3 = x_6;
goto _start;
}
block_12:
{
if (x_9 == 0)
{
goto block_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fget(x_2, x_3);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
block_16:
{
uint8_t x_15; 
x_15 = lean_name_eq(x_13, x_14);
lean_dec(x_14);
x_9 = x_15;
goto block_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_5 = x_1;
} else {
 lean_dec_ref(x_1);
 x_5 = lean_box(0);
}
x_6 = l_Lean_PersistentHashMap_instInhabitedEntry(lean_box(0), lean_box(0), lean_box(0));
x_7 = lean_unsigned_to_nat(5u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_shift_left(x_10, x_8);
x_12 = lean_usize_sub(x_11, x_10);
x_13 = lean_usize_land(x_2, x_12);
x_14 = lean_usize_to_nat(x_13);
x_15 = lean_array_get(x_6, x_4, x_14);
lean_dec(x_14);
lean_dec(x_4);
switch (lean_obj_tag(x_15)) {
case 0:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_22; lean_object* x_23; lean_object* x_26; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_16, sizeof(void*)*1 + 1);
lean_dec(x_16);
x_33 = lean_name_eq(x_29, x_31);
lean_dec(x_31);
if (x_33 == 0)
{
x_18 = x_33;
goto block_21;
}
else
{
if (x_30 == 0)
{
if (x_32 == 0)
{
x_18 = x_33;
goto block_21;
}
else
{
lean_object* x_34; 
lean_dec(x_17);
lean_dec(x_5);
x_34 = lean_box(0);
return x_34;
}
}
else
{
x_18 = x_32;
goto block_21;
}
}
}
else
{
lean_object* x_35; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_5);
x_35 = lean_box(0);
return x_35;
}
}
else
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_36; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_5);
x_36 = lean_box(0);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_3, 0);
x_26 = x_37;
goto block_28;
}
}
block_21:
{
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_5);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; 
if (lean_is_scalar(x_5)) {
 x_20 = lean_alloc_ctor(1, 1, 0);
} else {
 x_20 = x_5;
 lean_ctor_set_tag(x_20, 1);
}
lean_ctor_set(x_20, 0, x_17);
return x_20;
}
}
block_25:
{
uint8_t x_24; 
x_24 = lean_name_eq(x_22, x_23);
lean_dec(x_23);
x_18 = x_24;
goto block_21;
}
block_28:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
x_22 = x_26;
x_23 = x_27;
goto block_25;
}
}
case 1:
{
lean_object* x_38; size_t x_39; 
lean_dec(x_5);
x_38 = lean_ctor_get(x_15, 0);
lean_inc(x_38);
lean_dec(x_15);
x_39 = lean_usize_shift_right(x_2, x_8);
x_1 = x_38;
x_2 = x_39;
goto _start;
}
default: 
{
lean_object* x_41; 
lean_dec(x_5);
x_41 = lean_box(0);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
lean_dec(x_1);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__0___redArg(x_42, x_43, x_44, x_3);
lean_dec(x_43);
lean_dec(x_42);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_7; 
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_10 == 0)
{
lean_object* x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = l_Lean_Name_hash___override(x_11);
x_13 = lean_unsigned_to_nat(13u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_mix_hash(x_12, x_14);
x_3 = x_15;
goto block_6;
}
else
{
lean_object* x_16; uint64_t x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = l_Lean_Name_hash___override(x_16);
x_18 = lean_unsigned_to_nat(11u);
x_19 = lean_uint64_of_nat(x_18);
x_20 = lean_uint64_mix_hash(x_17, x_19);
x_3 = x_20;
goto block_6;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_2, 0);
x_7 = x_21;
goto block_9;
}
block_6:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
block_9:
{
uint64_t x_8; 
x_8 = l_Lean_Name_hash___override(x_7);
x_3 = x_8;
goto block_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_isDiagnosticsEnabled___redArg(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_40; 
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_st_ref_take(x_2, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_16, 4);
lean_inc(x_22);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 x_23 = x_16;
} else {
 lean_dec_ref(x_16);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_inc(x_24);
x_40 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0___redArg(x_24, x_1);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_unsigned_to_nat(1u);
x_25 = x_41;
goto block_39;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_42, x_43);
lean_dec(x_42);
x_25 = x_44;
goto block_39;
}
block_39:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
x_27 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_SimpTheorems_eraseCore_spec__1___redArg(x_24, x_1, x_25);
x_28 = lean_ctor_get(x_22, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 3);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_30, 3, x_29);
if (lean_is_scalar(x_23)) {
 x_31 = lean_alloc_ctor(0, 5, 0);
} else {
 x_31 = x_23;
}
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_19);
lean_ctor_set(x_31, 2, x_20);
lean_ctor_set(x_31, 3, x_21);
lean_ctor_set(x_31, 4, x_30);
x_32 = lean_st_ref_set(x_2, x_31, x_17);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_recordTriedSimpTheorem___redArg(x_1, x_4, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_recordTriedSimpTheorem___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_recordTriedSimpTheorem(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_27; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = l_Lean_isDiagnosticsEnabled___redArg(x_3, x_5);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_27 = x_45;
goto block_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_67; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_st_ref_take(x_2, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_48, 3);
lean_inc(x_53);
x_54 = lean_ctor_get(x_48, 4);
lean_inc(x_54);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 lean_ctor_release(x_48, 4);
 x_55 = x_48;
} else {
 lean_dec_ref(x_48);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_inc(x_56);
x_67 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Simp_recordTriedSimpTheorem_spec__0___redArg(x_56, x_1);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_unsigned_to_nat(1u);
x_57 = x_68;
goto block_66;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_69, x_70);
lean_dec(x_69);
x_57 = x_71;
goto block_66;
}
block_66:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_inc(x_1);
x_58 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_SimpTheorems_eraseCore_spec__1___redArg(x_56, x_1, x_57);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_54, 3);
lean_inc(x_61);
lean_dec(x_54);
x_62 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_59);
lean_ctor_set(x_62, 2, x_60);
lean_ctor_set(x_62, 3, x_61);
if (lean_is_scalar(x_55)) {
 x_63 = lean_alloc_ctor(0, 5, 0);
} else {
 x_63 = x_55;
}
lean_ctor_set(x_63, 0, x_50);
lean_ctor_set(x_63, 1, x_51);
lean_ctor_set(x_63, 2, x_52);
lean_ctor_set(x_63, 3, x_53);
lean_ctor_set(x_63, 4, x_62);
x_64 = lean_st_ref_set(x_2, x_63, x_49);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_27 = x_65;
goto block_41;
}
}
block_26:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_9 = lean_st_ref_take(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 2);
lean_inc(x_14);
x_15 = l_Lean_Meta_Simp_UsedSimps_insert(x_14, x_6);
x_16 = lean_ctor_get(x_10, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 4);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_16);
lean_ctor_set(x_18, 4, x_17);
x_19 = lean_st_ref_set(x_7, x_18, x_11);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
block_41:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_28; 
x_28 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_31 = l_Lean_Meta_isEqnThm_x3f(x_29, x_3, x_4, x_27);
lean_dec(x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_6 = x_1;
x_7 = x_2;
x_8 = x_33;
goto block_26;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_1, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
lean_dec(x_32);
lean_ctor_set(x_1, 0, x_37);
x_6 = x_1;
x_7 = x_2;
x_8 = x_36;
goto block_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_dec(x_31);
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
lean_dec(x_32);
x_40 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_30);
lean_ctor_set_uint8(x_40, sizeof(void*)*1 + 1, x_28);
x_6 = x_40;
x_7 = x_2;
x_8 = x_38;
goto block_26;
}
}
}
else
{
x_6 = x_1;
x_7 = x_2;
x_8 = x_27;
goto block_26;
}
}
else
{
x_6 = x_1;
x_7 = x_2;
x_8 = x_27;
goto block_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_recordSimpTheorem___redArg(x_1, x_4, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Simp_recordSimpTheorem___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_recordSimpTheorem(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_isDiagnosticsEnabled___redArg(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_40; 
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_st_ref_take(x_2, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_16, 4);
lean_inc(x_22);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 x_23 = x_16;
} else {
 lean_dec_ref(x_16);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_22, 2);
lean_inc(x_24);
lean_inc(x_24);
x_40 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0(lean_box(0), x_24, x_1);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_unsigned_to_nat(1u);
x_25 = x_41;
goto block_39;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_42, x_43);
lean_dec(x_42);
x_25 = x_44;
goto block_39;
}
block_39:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
x_28 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_24, x_1, x_25);
x_29 = lean_ctor_get(x_22, 3);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_30, 3, x_29);
if (lean_is_scalar(x_23)) {
 x_31 = lean_alloc_ctor(0, 5, 0);
} else {
 x_31 = x_23;
}
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_19);
lean_ctor_set(x_31, 2, x_20);
lean_ctor_set(x_31, 3, x_21);
lean_ctor_set(x_31, 4, x_30);
x_32 = lean_st_ref_set(x_2, x_31, x_17);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_recordCongrTheorem___redArg(x_1, x_4, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_recordCongrTheorem___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordCongrTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_recordCongrTheorem(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
return x_7;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ptr_addr(x_1);
x_8 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
goto _start;
}
else
{
return x_9;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
if (x_6 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = lean_usize_of_nat(x_4);
x_8 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_9 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0_spec__0(x_1, x_3, x_7, x_8);
return x_9;
}
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_10);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_12);
return x_13;
}
else
{
if (x_13 == 0)
{
lean_dec(x_12);
return x_13;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = lean_usize_of_nat(x_11);
x_15 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_16 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0_spec__1(x_1, x_10, x_14, x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_dec(x_7);
return x_4;
}
else
{
if (x_8 == 0)
{
lean_dec(x_7);
return x_4;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = lean_usize_of_nat(x_6);
x_10 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_11 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0_spec__1(x_1, x_5, x_9, x_10);
return x_11;
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 3);
x_4 = l_Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0_spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentArray_anyMAux___at___Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentArray_anyM___at___Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_isDiagnosticsEnabled___redArg(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_34; 
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_st_ref_take(x_2, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_16, 4);
lean_inc(x_22);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 x_23 = x_16;
} else {
 lean_dec_ref(x_16);
 x_23 = lean_box(0);
}
x_34 = l_Lean_Meta_Simp_recordTheoremWithBadKeys_unsafe__1(x_1, x_22);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_22, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_22, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_22, 3);
lean_inc(x_38);
lean_dec(x_22);
x_39 = l_Lean_PersistentArray_push___redArg(x_38, x_1);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set(x_40, 3, x_39);
x_24 = x_40;
goto block_33;
}
else
{
lean_dec(x_1);
x_24 = x_22;
goto block_33;
}
block_33:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 5, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set(x_25, 4, x_24);
x_26 = lean_st_ref_set(x_2, x_25, x_17);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_recordTheoremWithBadKeys___redArg(x_1, x_4, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_recordTheoremWithBadKeys___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_recordTheoremWithBadKeys(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Meta_mkEqRefl(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_getProof_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_10 = l_Lean_Meta_isExprDefEq(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_14 = l_Lean_Meta_mkEqRefl(x_9, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Meta_mkEq(x_1, x_9, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_mkExpectedTypeHint(x_15, x_18, x_3, x_4, x_5, x_6, x_19);
return x_20;
}
else
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
}
else
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = l_Lean_Meta_mkEqRefl(x_9, x_3, x_4, x_5, x_6, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_ctor_get(x_8, 0);
lean_inc(x_27);
lean_dec(x_8);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_7);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkCast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_Simp_Result_getProof(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_mk_string_unchecked("cast", 4, 4);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_mk_empty_array_with_capacity(x_13);
x_15 = lean_array_push(x_14, x_9);
x_16 = lean_array_push(x_15, x_2);
x_17 = l_Lean_Meta_mkAppM(x_12, x_16, x_3, x_4, x_5, x_6, x_10);
return x_17;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_mkEqMPR(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_expr_eqv(x_14, x_2);
lean_dec(x_14);
if (x_15 == 0)
{
goto block_12;
}
else
{
lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
else
{
lean_dec(x_13);
goto block_12;
}
block_12:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_Simp_Result_getProof(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_mkEqMPR(x_9, x_2, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Expr_app___override(x_9, x_2);
x_11 = lean_box(1);
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_8);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_2);
x_17 = l_Lean_Meta_mkCongrFun(x_16, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lean_Expr_app___override(x_20, x_2);
lean_ctor_set(x_8, 0, x_19);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_8);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_24);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lean_Expr_app___override(x_27, x_2);
lean_ctor_set(x_8, 0, x_25);
x_29 = lean_box(1);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_8);
x_31 = lean_unbox(x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
return x_17;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_17, 0);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_17);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_8, 0);
lean_inc(x_37);
lean_dec(x_8);
lean_inc(x_2);
x_38 = l_Lean_Meta_mkCongrFun(x_37, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
lean_dec(x_1);
x_43 = l_Lean_Expr_app___override(x_42, x_2);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_45 = lean_box(1);
x_46 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_47);
if (lean_is_scalar(x_41)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_41;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_40);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_ctor_get(x_38, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_51 = x_38;
} else {
 lean_dec_ref(x_38);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_Expr_app___override(x_1, x_9);
x_11 = lean_box(1);
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_8);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_1);
x_17 = l_Lean_Meta_mkCongrArg(x_1, x_16, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = l_Lean_Expr_app___override(x_1, x_20);
lean_ctor_set(x_8, 0, x_19);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_8);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_24);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
lean_dec(x_2);
x_28 = l_Lean_Expr_app___override(x_1, x_27);
lean_ctor_set(x_8, 0, x_25);
x_29 = lean_box(1);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_8);
x_31 = lean_unbox(x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
return x_17;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_17, 0);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_17);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_8, 0);
lean_inc(x_37);
lean_dec(x_8);
lean_inc(x_1);
x_38 = l_Lean_Meta_mkCongrArg(x_1, x_37, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
lean_dec(x_2);
x_43 = l_Lean_Expr_app___override(x_1, x_42);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_45 = lean_box(1);
x_46 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_47);
if (lean_is_scalar(x_41)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_41;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_40);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_ctor_get(x_38, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_51 = x_38;
} else {
 lean_dec_ref(x_38);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_Lean_Expr_app___override(x_8, x_9);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = l_Lean_Meta_mkCongrArg(x_8, x_18, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_12, 0, x_21);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_12);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_24);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
lean_ctor_set(x_12, 0, x_25);
x_27 = lean_box(1);
x_28 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_12);
x_29 = lean_unbox(x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_12);
lean_dec(x_10);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_12, 0);
lean_inc(x_35);
lean_dec(x_12);
x_36 = l_Lean_Meta_mkCongrArg(x_8, x_35, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_41 = lean_box(1);
x_42 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_42, 0, x_10);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_unbox(x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_43);
if (lean_is_scalar(x_39)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_39;
}
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_38);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_10);
x_45 = lean_ctor_get(x_36, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_36, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_47 = x_36;
} else {
 lean_dec_ref(x_36);
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
}
else
{
lean_object* x_49; 
lean_dec(x_8);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
lean_dec(x_2);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_11);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_11, 0);
x_52 = l_Lean_Meta_mkCongrFun(x_51, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_52, 0);
lean_ctor_set(x_11, 0, x_54);
x_55 = lean_box(1);
x_56 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_56, 0, x_10);
lean_ctor_set(x_56, 1, x_11);
x_57 = lean_unbox(x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_57);
lean_ctor_set(x_52, 0, x_56);
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_52);
lean_ctor_set(x_11, 0, x_58);
x_60 = lean_box(1);
x_61 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_61, 0, x_10);
lean_ctor_set(x_61, 1, x_11);
x_62 = lean_unbox(x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_62);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_59);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_free_object(x_11);
lean_dec(x_10);
x_64 = !lean_is_exclusive(x_52);
if (x_64 == 0)
{
return x_52;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_52, 0);
x_66 = lean_ctor_get(x_52, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_52);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_11, 0);
lean_inc(x_68);
lean_dec(x_11);
x_69 = l_Lean_Meta_mkCongrFun(x_68, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; 
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
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_70);
x_74 = lean_box(1);
x_75 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_75, 0, x_10);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_unbox(x_74);
lean_ctor_set_uint8(x_75, sizeof(void*)*2, x_76);
if (lean_is_scalar(x_72)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_72;
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_71);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_10);
x_78 = lean_ctor_get(x_69, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_69, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_80 = x_69;
} else {
 lean_dec_ref(x_69);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
lean_object* x_82; uint8_t x_83; 
lean_dec(x_9);
x_82 = lean_ctor_get(x_11, 0);
lean_inc(x_82);
lean_dec(x_11);
x_83 = !lean_is_exclusive(x_49);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_49, 0);
x_85 = l_Lean_Meta_mkCongr(x_82, x_84, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_85, 0);
lean_ctor_set(x_49, 0, x_87);
x_88 = lean_box(1);
x_89 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_89, 0, x_10);
lean_ctor_set(x_89, 1, x_49);
x_90 = lean_unbox(x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*2, x_90);
lean_ctor_set(x_85, 0, x_89);
return x_85;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_85, 0);
x_92 = lean_ctor_get(x_85, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_85);
lean_ctor_set(x_49, 0, x_91);
x_93 = lean_box(1);
x_94 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_94, 0, x_10);
lean_ctor_set(x_94, 1, x_49);
x_95 = lean_unbox(x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*2, x_95);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_92);
return x_96;
}
}
else
{
uint8_t x_97; 
lean_free_object(x_49);
lean_dec(x_10);
x_97 = !lean_is_exclusive(x_85);
if (x_97 == 0)
{
return x_85;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_85, 0);
x_99 = lean_ctor_get(x_85, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_85);
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
x_101 = lean_ctor_get(x_49, 0);
lean_inc(x_101);
lean_dec(x_49);
x_102 = l_Lean_Meta_mkCongr(x_82, x_101, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_103);
x_107 = lean_box(1);
x_108 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_108, 0, x_10);
lean_ctor_set(x_108, 1, x_106);
x_109 = lean_unbox(x_107);
lean_ctor_set_uint8(x_108, sizeof(void*)*2, x_109);
if (lean_is_scalar(x_105)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_105;
}
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_104);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_10);
x_111 = lean_ctor_get(x_102, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_102, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_113 = x_102;
} else {
 lean_dec_ref(x_102);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkImpCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_48; 
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_1, 2);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_60 = l_Lean_Expr_forallE___override(x_56, x_57, x_58, x_59);
if (lean_obj_tag(x_60) == 7)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; size_t x_72; size_t x_73; uint8_t x_74; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 2);
lean_inc(x_63);
x_64 = lean_ctor_get_uint8(x_60, sizeof(void*)*3 + 8);
x_65 = lean_ctor_get(x_2, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_3, 0);
lean_inc(x_66);
x_72 = lean_ptr_addr(x_62);
lean_dec(x_62);
x_73 = lean_ptr_addr(x_65);
x_74 = lean_usize_dec_eq(x_72, x_73);
if (x_74 == 0)
{
lean_dec(x_63);
x_67 = x_74;
goto block_71;
}
else
{
size_t x_75; size_t x_76; uint8_t x_77; 
x_75 = lean_ptr_addr(x_63);
lean_dec(x_63);
x_76 = lean_ptr_addr(x_66);
x_77 = lean_usize_dec_eq(x_75, x_76);
x_67 = x_77;
goto block_71;
}
block_71:
{
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_60);
x_68 = l_Lean_Expr_forallE___override(x_61, x_65, x_66, x_59);
x_48 = x_68;
goto block_55;
}
else
{
uint8_t x_69; 
x_69 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_64, x_59);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_60);
x_70 = l_Lean_Expr_forallE___override(x_61, x_65, x_66, x_59);
x_48 = x_70;
goto block_55;
}
else
{
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_61);
x_48 = x_60;
goto block_55;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_60);
x_78 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_79 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateForall!Impl", 48, 48);
x_80 = lean_unsigned_to_nat(1828u);
x_81 = lean_unsigned_to_nat(23u);
x_82 = lean_mk_string_unchecked("forall expected", 15, 15);
x_83 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_78, x_79, x_80, x_81, x_82);
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_78);
x_84 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_83);
x_48 = x_84;
goto block_55;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_1);
x_85 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_86 = lean_mk_string_unchecked("Lean.Expr.updateForallE!", 24, 24);
x_87 = lean_unsigned_to_nat(1839u);
x_88 = lean_unsigned_to_nat(24u);
x_89 = lean_mk_string_unchecked("forall expected", 15, 15);
x_90 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_85, x_86, x_87, x_88, x_89);
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_85);
x_91 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_90);
x_48 = x_91;
goto block_55;
}
block_47:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_15 = l_Lean_Meta_Simp_Result_getProof(x_2, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_18 = l_Lean_Meta_Simp_Result_getProof(x_3, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_mkImpCongr(x_16, x_19, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_box(1);
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_27);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_box(1);
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_9);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_unbox(x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_9);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_15);
if (x_43 == 0)
{
return x_15;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_15, 0);
x_45 = lean_ctor_get(x_15, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_15);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
block_55:
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_box(1);
x_52 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_unbox(x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_53);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_8);
return x_54;
}
else
{
lean_dec(x_50);
x_9 = x_48;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
x_14 = x_8;
goto block_47;
}
}
else
{
lean_dec(x_49);
x_9 = x_48;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
x_14 = x_8;
goto block_47;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_mk_string_unchecked("Eq", 2, 2);
x_10 = lean_mk_string_unchecked("rec", 3, 3);
lean_inc(x_9);
x_11 = l_Lean_Name_mkStr2(x_9, x_10);
x_12 = lean_unsigned_to_nat(6u);
x_13 = l_Lean_Expr_isAppOfArity(x_1, x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_mk_string_unchecked("ndrec", 5, 5);
x_15 = l_Lean_Name_mkStr2(x_9, x_14);
x_16 = l_Lean_Expr_isAppOfArity(x_1, x_15, x_12);
lean_dec(x_15);
x_2 = x_16;
goto block_8;
}
else
{
lean_dec(x_9);
x_2 = x_13;
goto block_8;
}
block_8:
{
if (x_2 == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = l_Lean_Expr_appArg_x21(x_1);
x_4 = lean_mk_string_unchecked("Eq", 2, 2);
x_5 = lean_mk_string_unchecked("refl", 4, 4);
x_6 = l_Lean_Name_mkStr2(x_4, x_5);
x_7 = l_Lean_Expr_isAppOf(x_3, x_6);
lean_dec(x_6);
lean_dec(x_3);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts_elimDummyEqRec(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Expr_appFn_x21(x_1);
lean_dec(x_1);
x_4 = l_Lean_Expr_appFn_x21(x_3);
lean_dec(x_3);
x_5 = l_Lean_Expr_appArg_x21(x_4);
lean_dec(x_4);
x_1 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_removeUnnecessaryCasts_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_nat_dec_lt(x_3, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = l_Lean_instInhabitedExpr;
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_array_get(x_14, x_15, x_3);
x_17 = l_Lean_Meta_Simp_removeUnnecessaryCasts_isDummyEqRec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_5 = x_19;
x_6 = x_4;
goto block_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_20 = l_Lean_Meta_Simp_removeUnnecessaryCasts_elimDummyEqRec(x_16);
x_21 = lean_array_set(x_15, x_3, x_20);
x_22 = lean_box(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_5 = x_23;
x_6 = x_4;
goto block_10;
}
}
block_10:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_nat_add(x_3, x_7);
lean_dec(x_3);
x_2 = x_5;
x_3 = x_8;
x_4 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_removeUnnecessaryCasts_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_removeUnnecessaryCasts_spec__0___redArg(x_1, x_2, x_3, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_7 = lean_box(0);
x_8 = l_Lean_Expr_sort___override(x_7);
x_9 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_9);
x_10 = lean_mk_array(x_9, x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_9, x_11);
lean_dec(x_9);
lean_inc(x_1);
x_13 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_10, x_12);
x_14 = lean_box(0);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_13);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
x_19 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_removeUnnecessaryCasts_spec__0___redArg(x_17, x_18, x_15, x_6);
lean_dec(x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_19, 0);
lean_dec(x_24);
lean_ctor_set(x_19, 0, x_1);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_19, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
lean_dec(x_20);
x_30 = l_Lean_Expr_getAppFn(x_1);
lean_dec(x_1);
x_31 = l_Lean_mkAppN(x_30, x_29);
lean_dec(x_29);
lean_ctor_set(x_19, 0, x_31);
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_dec(x_19);
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
lean_dec(x_20);
x_34 = l_Lean_Expr_getAppFn(x_1);
lean_dec(x_1);
x_35 = l_Lean_mkAppN(x_34, x_33);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_removeUnnecessaryCasts_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_removeUnnecessaryCasts_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_removeUnnecessaryCasts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_removeUnnecessaryCasts_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_removeUnnecessaryCasts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_removeUnnecessaryCasts(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 12);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_checkTraceOption(x_4, x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_1, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_take(x_6, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; double x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_5, 5);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 3);
lean_inc(x_19);
x_20 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_float_of_nat(x_22);
x_24 = lean_box(0);
x_25 = lean_mk_string_unchecked("", 0, 0);
x_26 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set_float(x_26, sizeof(void*)*2, x_23);
lean_ctor_set_float(x_26, sizeof(void*)*2 + 8, x_23);
x_27 = lean_unbox(x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 16, x_27);
x_28 = lean_mk_empty_array_with_capacity(x_22);
x_29 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_9);
lean_ctor_set(x_29, 2, x_28);
lean_inc(x_15);
lean_ctor_set(x_11, 1, x_29);
lean_ctor_set(x_11, 0, x_15);
x_30 = l_Lean_PersistentArray_push___redArg(x_21, x_11);
x_31 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_uint64(x_31, sizeof(void*)*1, x_20);
x_32 = lean_ctor_get(x_13, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_13, 5);
lean_inc(x_33);
x_34 = lean_ctor_get(x_13, 6);
lean_inc(x_34);
x_35 = lean_ctor_get(x_13, 7);
lean_inc(x_35);
lean_dec(x_13);
x_36 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_36, 0, x_16);
lean_ctor_set(x_36, 1, x_17);
lean_ctor_set(x_36, 2, x_18);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_32);
lean_ctor_set(x_36, 5, x_33);
lean_ctor_set(x_36, 6, x_34);
lean_ctor_set(x_36, 7, x_35);
x_37 = lean_st_ref_set(x_6, x_36, x_14);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint64_t x_51; lean_object* x_52; lean_object* x_53; double x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_46 = lean_ctor_get(x_5, 5);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_44, 3);
lean_inc(x_50);
x_51 = lean_ctor_get_uint64(x_50, sizeof(void*)*1);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_float_of_nat(x_53);
x_55 = lean_box(0);
x_56 = lean_mk_string_unchecked("", 0, 0);
x_57 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_float(x_57, sizeof(void*)*2, x_54);
lean_ctor_set_float(x_57, sizeof(void*)*2 + 8, x_54);
x_58 = lean_unbox(x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*2 + 16, x_58);
x_59 = lean_mk_empty_array_with_capacity(x_53);
x_60 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_9);
lean_ctor_set(x_60, 2, x_59);
lean_inc(x_46);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_46);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentArray_push___redArg(x_52, x_61);
x_63 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_uint64(x_63, sizeof(void*)*1, x_51);
x_64 = lean_ctor_get(x_44, 4);
lean_inc(x_64);
x_65 = lean_ctor_get(x_44, 5);
lean_inc(x_65);
x_66 = lean_ctor_get(x_44, 6);
lean_inc(x_66);
x_67 = lean_ctor_get(x_44, 7);
lean_inc(x_67);
lean_dec(x_44);
x_68 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_68, 0, x_47);
lean_ctor_set(x_68, 1, x_48);
lean_ctor_set(x_68, 2, x_49);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set(x_68, 4, x_64);
lean_ctor_set(x_68, 5, x_65);
lean_ctor_set(x_68, 6, x_66);
lean_ctor_set(x_68, 7, x_67);
x_69 = lean_st_ref_set(x_6, x_68, x_45);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_5, x_4);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_14);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_26 = lean_array_uget(x_3, x_5);
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
x_127 = lean_ctor_get(x_6, 1);
lean_inc(x_127);
lean_dec(x_6);
x_128 = lean_array_get_size(x_1);
x_129 = lean_nat_dec_lt(x_27, x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_128);
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_131 = lean_infer_type(x_130, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_134 = l_Lean_Meta_whnfD(x_132, x_10, x_11, x_12, x_13, x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = l_Lean_Expr_isArrow(x_135);
lean_dec(x_135);
if (x_137 == 0)
{
lean_object* x_138; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_138 = lean_dsimp(x_26, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_136);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_141 = l_Lean_Meta_Simp_mkCongrFun(x_127, x_139, x_10, x_11, x_12, x_13, x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_box(0);
x_145 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2___lam__0(x_27, x_142, x_144, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_143);
lean_dec(x_27);
x_15 = x_145;
goto block_23;
}
else
{
uint8_t x_146; 
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_146 = !lean_is_exclusive(x_141);
if (x_146 == 0)
{
return x_141;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_141, 0);
x_148 = lean_ctor_get(x_141, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_141);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_127);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_150 = !lean_is_exclusive(x_138);
if (x_150 == 0)
{
return x_138;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_138, 0);
x_152 = lean_ctor_get(x_138, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_138);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
lean_object* x_154; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_154 = lean_simp(x_26, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_136);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_157 = l_Lean_Meta_Simp_mkCongr(x_127, x_155, x_10, x_11, x_12, x_13, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_box(0);
x_161 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2___lam__0(x_27, x_158, x_160, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_159);
lean_dec(x_27);
x_15 = x_161;
goto block_23;
}
else
{
uint8_t x_162; 
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_162 = !lean_is_exclusive(x_157);
if (x_162 == 0)
{
return x_157;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_157, 0);
x_164 = lean_ctor_get(x_157, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_157);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_127);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_166 = !lean_is_exclusive(x_154);
if (x_166 == 0)
{
return x_154;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_154, 0);
x_168 = lean_ctor_get(x_154, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_154);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_127);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_170 = !lean_is_exclusive(x_134);
if (x_170 == 0)
{
return x_134;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_134, 0);
x_172 = lean_ctor_get(x_134, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_134);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_127);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_174 = !lean_is_exclusive(x_131);
if (x_174 == 0)
{
return x_131;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_131, 0);
x_176 = lean_ctor_get(x_131, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_131);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_178 = lean_mk_string_unchecked("Debug", 5, 5);
x_179 = lean_mk_string_unchecked("Meta", 4, 4);
x_180 = lean_mk_string_unchecked("Tactic", 6, 6);
x_181 = lean_mk_string_unchecked("simp", 4, 4);
x_182 = l_Lean_Name_mkStr4(x_178, x_179, x_180, x_181);
lean_inc(x_182);
x_183 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_182, x_12, x_14);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_unbox(x_184);
lean_dec(x_184);
if (x_185 == 0)
{
lean_object* x_186; 
lean_dec(x_182);
lean_dec(x_128);
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
lean_dec(x_183);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_114 = x_127;
x_115 = x_7;
x_116 = x_8;
x_117 = x_9;
x_118 = x_10;
x_119 = x_11;
x_120 = x_12;
x_121 = x_13;
x_122 = x_186;
goto block_126;
}
else
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_183);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_220; uint8_t x_221; 
x_188 = lean_ctor_get(x_183, 1);
x_189 = lean_ctor_get(x_183, 0);
lean_dec(x_189);
x_190 = lean_mk_string_unchecked("app [", 5, 5);
x_191 = l_Lean_stringToMessageData(x_190);
lean_dec(x_190);
lean_inc(x_27);
x_192 = l___private_Init_Data_Repr_0__Nat_reprFast(x_27);
x_193 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_193, 0, x_192);
x_194 = l_Lean_MessageData_ofFormat(x_193);
lean_ctor_set_tag(x_183, 7);
lean_ctor_set(x_183, 1, x_194);
lean_ctor_set(x_183, 0, x_191);
x_195 = lean_mk_string_unchecked("] ", 2, 2);
x_196 = l_Lean_stringToMessageData(x_195);
lean_dec(x_195);
x_197 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_197, 0, x_183);
lean_ctor_set(x_197, 1, x_196);
x_198 = l___private_Init_Data_Repr_0__Nat_reprFast(x_128);
x_199 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_199, 0, x_198);
x_200 = l_Lean_MessageData_ofFormat(x_199);
x_201 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_201, 0, x_197);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_mk_string_unchecked(" ", 1, 1);
x_203 = l_Lean_stringToMessageData(x_202);
lean_dec(x_202);
x_204 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_203);
lean_inc(x_26);
x_205 = l_Lean_MessageData_ofExpr(x_26);
x_206 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_mk_string_unchecked(" hasFwdDeps: ", 13, 13);
x_208 = l_Lean_stringToMessageData(x_207);
lean_dec(x_207);
x_209 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_208);
x_220 = lean_array_fget(x_1, x_27);
x_221 = lean_ctor_get_uint8(x_220, sizeof(void*)*1 + 1);
lean_dec(x_220);
if (x_221 == 0)
{
lean_object* x_222; 
x_222 = lean_mk_string_unchecked("false", 5, 5);
x_210 = x_222;
goto block_219;
}
else
{
lean_object* x_223; 
x_223 = lean_mk_string_unchecked("true", 4, 4);
x_210 = x_223;
goto block_219;
}
block_219:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_211 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_211, 0, x_210);
x_212 = l_Lean_MessageData_ofFormat(x_211);
x_213 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_213, 0, x_209);
lean_ctor_set(x_213, 1, x_212);
x_214 = lean_mk_string_unchecked("", 0, 0);
x_215 = l_Lean_stringToMessageData(x_214);
lean_dec(x_214);
x_216 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_215);
x_217 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_182, x_216, x_10, x_11, x_12, x_13, x_188);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_114 = x_127;
x_115 = x_7;
x_116 = x_8;
x_117 = x_9;
x_118 = x_10;
x_119 = x_11;
x_120 = x_12;
x_121 = x_13;
x_122 = x_218;
goto block_126;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_256; uint8_t x_257; 
x_224 = lean_ctor_get(x_183, 1);
lean_inc(x_224);
lean_dec(x_183);
x_225 = lean_mk_string_unchecked("app [", 5, 5);
x_226 = l_Lean_stringToMessageData(x_225);
lean_dec(x_225);
lean_inc(x_27);
x_227 = l___private_Init_Data_Repr_0__Nat_reprFast(x_27);
x_228 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_228, 0, x_227);
x_229 = l_Lean_MessageData_ofFormat(x_228);
x_230 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_230, 0, x_226);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_mk_string_unchecked("] ", 2, 2);
x_232 = l_Lean_stringToMessageData(x_231);
lean_dec(x_231);
x_233 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_232);
x_234 = l___private_Init_Data_Repr_0__Nat_reprFast(x_128);
x_235 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_235, 0, x_234);
x_236 = l_Lean_MessageData_ofFormat(x_235);
x_237 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_237, 0, x_233);
lean_ctor_set(x_237, 1, x_236);
x_238 = lean_mk_string_unchecked(" ", 1, 1);
x_239 = l_Lean_stringToMessageData(x_238);
lean_dec(x_238);
x_240 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_239);
lean_inc(x_26);
x_241 = l_Lean_MessageData_ofExpr(x_26);
x_242 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_mk_string_unchecked(" hasFwdDeps: ", 13, 13);
x_244 = l_Lean_stringToMessageData(x_243);
lean_dec(x_243);
x_245 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_244);
x_256 = lean_array_fget(x_1, x_27);
x_257 = lean_ctor_get_uint8(x_256, sizeof(void*)*1 + 1);
lean_dec(x_256);
if (x_257 == 0)
{
lean_object* x_258; 
x_258 = lean_mk_string_unchecked("false", 5, 5);
x_246 = x_258;
goto block_255;
}
else
{
lean_object* x_259; 
x_259 = lean_mk_string_unchecked("true", 4, 4);
x_246 = x_259;
goto block_255;
}
block_255:
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_247 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_247, 0, x_246);
x_248 = l_Lean_MessageData_ofFormat(x_247);
x_249 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_249, 0, x_245);
lean_ctor_set(x_249, 1, x_248);
x_250 = lean_mk_string_unchecked("", 0, 0);
x_251 = l_Lean_stringToMessageData(x_250);
lean_dec(x_250);
x_252 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_251);
x_253 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_182, x_252, x_10, x_11, x_12, x_13, x_224);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
lean_dec(x_253);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_114 = x_127;
x_115 = x_7;
x_116 = x_8;
x_117 = x_9;
x_118 = x_10;
x_119 = x_11;
x_120 = x_12;
x_121 = x_13;
x_122 = x_254;
goto block_126;
}
}
}
}
block_113:
{
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = lean_ctor_get_uint8(x_29, sizeof(void*)*1 + 1);
lean_dec(x_29);
if (x_39 == 0)
{
lean_object* x_40; 
lean_inc(x_37);
lean_inc(x_32);
lean_inc(x_28);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_31);
x_40 = lean_simp(x_26, x_31, x_33, x_34, x_35, x_28, x_32, x_37, x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_37);
lean_inc(x_32);
lean_inc(x_28);
lean_inc(x_35);
x_43 = l_Lean_Meta_Simp_mkCongr(x_30, x_41, x_35, x_28, x_32, x_37, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_box(0);
x_47 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2___lam__0(x_27, x_44, x_46, x_31, x_33, x_34, x_35, x_28, x_32, x_37, x_45);
lean_dec(x_37);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_27);
x_15 = x_47;
goto block_23;
}
else
{
uint8_t x_48; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
return x_43;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_43, 0);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_43);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_52 = !lean_is_exclusive(x_40);
if (x_52 == 0)
{
return x_40;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_40, 0);
x_54 = lean_ctor_get(x_40, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_40);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_30, 0);
lean_inc(x_56);
lean_inc(x_37);
lean_inc(x_32);
lean_inc(x_28);
lean_inc(x_35);
x_57 = lean_infer_type(x_56, x_35, x_28, x_32, x_37, x_36);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_37);
lean_inc(x_32);
lean_inc(x_28);
x_60 = l_Lean_Meta_whnfD(x_58, x_35, x_28, x_32, x_37, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Expr_isArrow(x_61);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; 
lean_inc(x_37);
lean_inc(x_32);
lean_inc(x_28);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_31);
x_64 = lean_dsimp(x_26, x_31, x_33, x_34, x_35, x_28, x_32, x_37, x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_37);
lean_inc(x_32);
lean_inc(x_28);
lean_inc(x_35);
x_67 = l_Lean_Meta_Simp_mkCongrFun(x_30, x_65, x_35, x_28, x_32, x_37, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_box(0);
x_71 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2___lam__0(x_27, x_68, x_70, x_31, x_33, x_34, x_35, x_28, x_32, x_37, x_69);
lean_dec(x_37);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_27);
x_15 = x_71;
goto block_23;
}
else
{
uint8_t x_72; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_72 = !lean_is_exclusive(x_67);
if (x_72 == 0)
{
return x_67;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_67, 0);
x_74 = lean_ctor_get(x_67, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_67);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_76 = !lean_is_exclusive(x_64);
if (x_76 == 0)
{
return x_64;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_64, 0);
x_78 = lean_ctor_get(x_64, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_64);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; 
lean_inc(x_37);
lean_inc(x_32);
lean_inc(x_28);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_31);
x_80 = lean_simp(x_26, x_31, x_33, x_34, x_35, x_28, x_32, x_37, x_62);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_37);
lean_inc(x_32);
lean_inc(x_28);
lean_inc(x_35);
x_83 = l_Lean_Meta_Simp_mkCongr(x_30, x_81, x_35, x_28, x_32, x_37, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_box(0);
x_87 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2___lam__0(x_27, x_84, x_86, x_31, x_33, x_34, x_35, x_28, x_32, x_37, x_85);
lean_dec(x_37);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_27);
x_15 = x_87;
goto block_23;
}
else
{
uint8_t x_88; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_88 = !lean_is_exclusive(x_83);
if (x_88 == 0)
{
return x_83;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_83, 0);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_83);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_92 = !lean_is_exclusive(x_80);
if (x_92 == 0)
{
return x_80;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_80, 0);
x_94 = lean_ctor_get(x_80, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_80);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_96 = !lean_is_exclusive(x_60);
if (x_96 == 0)
{
return x_60;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_60, 0);
x_98 = lean_ctor_get(x_60, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_60);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_100 = !lean_is_exclusive(x_57);
if (x_100 == 0)
{
return x_57;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_57, 0);
x_102 = lean_ctor_get(x_57, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_57);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
else
{
lean_object* x_104; 
lean_dec(x_29);
lean_inc(x_37);
lean_inc(x_32);
lean_inc(x_28);
lean_inc(x_35);
x_104 = l_Lean_Meta_Simp_mkCongrFun(x_30, x_26, x_35, x_28, x_32, x_37, x_36);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_box(0);
x_108 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2___lam__0(x_27, x_105, x_107, x_31, x_33, x_34, x_35, x_28, x_32, x_37, x_106);
lean_dec(x_37);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_27);
x_15 = x_108;
goto block_23;
}
else
{
uint8_t x_109; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_109 = !lean_is_exclusive(x_104);
if (x_109 == 0)
{
return x_104;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_104, 0);
x_111 = lean_ctor_get(x_104, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_104);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
block_126:
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_array_fget(x_1, x_27);
x_124 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 14);
if (x_124 == 0)
{
x_28 = x_119;
x_29 = x_123;
x_30 = x_114;
x_31 = x_115;
x_32 = x_120;
x_33 = x_116;
x_34 = x_117;
x_35 = x_118;
x_36 = x_122;
x_37 = x_121;
x_38 = x_124;
goto block_113;
}
else
{
uint8_t x_125; 
x_125 = l_Lean_Meta_ParamInfo_isInstImplicit(x_123);
x_28 = x_119;
x_29 = x_123;
x_30 = x_114;
x_31 = x_115;
x_32 = x_120;
x_33 = x_116;
x_34 = x_117;
x_35 = x_118;
x_36 = x_122;
x_37 = x_121;
x_38 = x_125;
goto block_113;
}
}
}
block_23:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_add(x_5, x_20);
x_5 = x_21;
x_6 = x_18;
x_14 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_5, x_4);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_14);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_26 = lean_array_uget(x_3, x_5);
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
x_127 = lean_ctor_get(x_6, 1);
lean_inc(x_127);
lean_dec(x_6);
x_128 = lean_array_get_size(x_1);
x_129 = lean_nat_dec_lt(x_27, x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_128);
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_131 = lean_infer_type(x_130, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_134 = l_Lean_Meta_whnfD(x_132, x_10, x_11, x_12, x_13, x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = l_Lean_Expr_isArrow(x_135);
lean_dec(x_135);
if (x_137 == 0)
{
lean_object* x_138; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_138 = lean_dsimp(x_26, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_136);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_141 = l_Lean_Meta_Simp_mkCongrFun(x_127, x_139, x_10, x_11, x_12, x_13, x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_box(0);
x_145 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2___lam__0(x_27, x_142, x_144, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_143);
lean_dec(x_27);
x_15 = x_145;
goto block_23;
}
else
{
uint8_t x_146; 
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_146 = !lean_is_exclusive(x_141);
if (x_146 == 0)
{
return x_141;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_141, 0);
x_148 = lean_ctor_get(x_141, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_141);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_127);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_150 = !lean_is_exclusive(x_138);
if (x_150 == 0)
{
return x_138;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_138, 0);
x_152 = lean_ctor_get(x_138, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_138);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
lean_object* x_154; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_154 = lean_simp(x_26, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_136);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_157 = l_Lean_Meta_Simp_mkCongr(x_127, x_155, x_10, x_11, x_12, x_13, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_box(0);
x_161 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2___lam__0(x_27, x_158, x_160, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_159);
lean_dec(x_27);
x_15 = x_161;
goto block_23;
}
else
{
uint8_t x_162; 
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_162 = !lean_is_exclusive(x_157);
if (x_162 == 0)
{
return x_157;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_157, 0);
x_164 = lean_ctor_get(x_157, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_157);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_127);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_166 = !lean_is_exclusive(x_154);
if (x_166 == 0)
{
return x_154;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_154, 0);
x_168 = lean_ctor_get(x_154, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_154);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_127);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_170 = !lean_is_exclusive(x_134);
if (x_170 == 0)
{
return x_134;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_134, 0);
x_172 = lean_ctor_get(x_134, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_134);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_127);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_174 = !lean_is_exclusive(x_131);
if (x_174 == 0)
{
return x_131;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_131, 0);
x_176 = lean_ctor_get(x_131, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_131);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_178 = lean_mk_string_unchecked("Debug", 5, 5);
x_179 = lean_mk_string_unchecked("Meta", 4, 4);
x_180 = lean_mk_string_unchecked("Tactic", 6, 6);
x_181 = lean_mk_string_unchecked("simp", 4, 4);
x_182 = l_Lean_Name_mkStr4(x_178, x_179, x_180, x_181);
lean_inc(x_182);
x_183 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_182, x_12, x_14);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_unbox(x_184);
lean_dec(x_184);
if (x_185 == 0)
{
lean_object* x_186; 
lean_dec(x_182);
lean_dec(x_128);
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
lean_dec(x_183);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_114 = x_127;
x_115 = x_7;
x_116 = x_8;
x_117 = x_9;
x_118 = x_10;
x_119 = x_11;
x_120 = x_12;
x_121 = x_13;
x_122 = x_186;
goto block_126;
}
else
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_183);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_220; uint8_t x_221; 
x_188 = lean_ctor_get(x_183, 1);
x_189 = lean_ctor_get(x_183, 0);
lean_dec(x_189);
x_190 = lean_mk_string_unchecked("app [", 5, 5);
x_191 = l_Lean_stringToMessageData(x_190);
lean_dec(x_190);
lean_inc(x_27);
x_192 = l___private_Init_Data_Repr_0__Nat_reprFast(x_27);
x_193 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_193, 0, x_192);
x_194 = l_Lean_MessageData_ofFormat(x_193);
lean_ctor_set_tag(x_183, 7);
lean_ctor_set(x_183, 1, x_194);
lean_ctor_set(x_183, 0, x_191);
x_195 = lean_mk_string_unchecked("] ", 2, 2);
x_196 = l_Lean_stringToMessageData(x_195);
lean_dec(x_195);
x_197 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_197, 0, x_183);
lean_ctor_set(x_197, 1, x_196);
x_198 = l___private_Init_Data_Repr_0__Nat_reprFast(x_128);
x_199 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_199, 0, x_198);
x_200 = l_Lean_MessageData_ofFormat(x_199);
x_201 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_201, 0, x_197);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_mk_string_unchecked(" ", 1, 1);
x_203 = l_Lean_stringToMessageData(x_202);
lean_dec(x_202);
x_204 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_203);
lean_inc(x_26);
x_205 = l_Lean_MessageData_ofExpr(x_26);
x_206 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_mk_string_unchecked(" hasFwdDeps: ", 13, 13);
x_208 = l_Lean_stringToMessageData(x_207);
lean_dec(x_207);
x_209 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_208);
x_220 = lean_array_fget(x_1, x_27);
x_221 = lean_ctor_get_uint8(x_220, sizeof(void*)*1 + 1);
lean_dec(x_220);
if (x_221 == 0)
{
lean_object* x_222; 
x_222 = lean_mk_string_unchecked("false", 5, 5);
x_210 = x_222;
goto block_219;
}
else
{
lean_object* x_223; 
x_223 = lean_mk_string_unchecked("true", 4, 4);
x_210 = x_223;
goto block_219;
}
block_219:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_211 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_211, 0, x_210);
x_212 = l_Lean_MessageData_ofFormat(x_211);
x_213 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_213, 0, x_209);
lean_ctor_set(x_213, 1, x_212);
x_214 = lean_mk_string_unchecked("", 0, 0);
x_215 = l_Lean_stringToMessageData(x_214);
lean_dec(x_214);
x_216 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_215);
x_217 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_182, x_216, x_10, x_11, x_12, x_13, x_188);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_114 = x_127;
x_115 = x_7;
x_116 = x_8;
x_117 = x_9;
x_118 = x_10;
x_119 = x_11;
x_120 = x_12;
x_121 = x_13;
x_122 = x_218;
goto block_126;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_256; uint8_t x_257; 
x_224 = lean_ctor_get(x_183, 1);
lean_inc(x_224);
lean_dec(x_183);
x_225 = lean_mk_string_unchecked("app [", 5, 5);
x_226 = l_Lean_stringToMessageData(x_225);
lean_dec(x_225);
lean_inc(x_27);
x_227 = l___private_Init_Data_Repr_0__Nat_reprFast(x_27);
x_228 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_228, 0, x_227);
x_229 = l_Lean_MessageData_ofFormat(x_228);
x_230 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_230, 0, x_226);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_mk_string_unchecked("] ", 2, 2);
x_232 = l_Lean_stringToMessageData(x_231);
lean_dec(x_231);
x_233 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_232);
x_234 = l___private_Init_Data_Repr_0__Nat_reprFast(x_128);
x_235 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_235, 0, x_234);
x_236 = l_Lean_MessageData_ofFormat(x_235);
x_237 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_237, 0, x_233);
lean_ctor_set(x_237, 1, x_236);
x_238 = lean_mk_string_unchecked(" ", 1, 1);
x_239 = l_Lean_stringToMessageData(x_238);
lean_dec(x_238);
x_240 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_239);
lean_inc(x_26);
x_241 = l_Lean_MessageData_ofExpr(x_26);
x_242 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_mk_string_unchecked(" hasFwdDeps: ", 13, 13);
x_244 = l_Lean_stringToMessageData(x_243);
lean_dec(x_243);
x_245 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_244);
x_256 = lean_array_fget(x_1, x_27);
x_257 = lean_ctor_get_uint8(x_256, sizeof(void*)*1 + 1);
lean_dec(x_256);
if (x_257 == 0)
{
lean_object* x_258; 
x_258 = lean_mk_string_unchecked("false", 5, 5);
x_246 = x_258;
goto block_255;
}
else
{
lean_object* x_259; 
x_259 = lean_mk_string_unchecked("true", 4, 4);
x_246 = x_259;
goto block_255;
}
block_255:
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_247 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_247, 0, x_246);
x_248 = l_Lean_MessageData_ofFormat(x_247);
x_249 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_249, 0, x_245);
lean_ctor_set(x_249, 1, x_248);
x_250 = lean_mk_string_unchecked("", 0, 0);
x_251 = l_Lean_stringToMessageData(x_250);
lean_dec(x_250);
x_252 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_251);
x_253 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_182, x_252, x_10, x_11, x_12, x_13, x_224);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
lean_dec(x_253);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_114 = x_127;
x_115 = x_7;
x_116 = x_8;
x_117 = x_9;
x_118 = x_10;
x_119 = x_11;
x_120 = x_12;
x_121 = x_13;
x_122 = x_254;
goto block_126;
}
}
}
}
block_113:
{
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = lean_ctor_get_uint8(x_36, sizeof(void*)*1 + 1);
lean_dec(x_36);
if (x_39 == 0)
{
lean_object* x_40; 
lean_inc(x_34);
lean_inc(x_32);
lean_inc(x_37);
lean_inc(x_33);
lean_inc(x_35);
lean_inc(x_28);
lean_inc(x_31);
x_40 = lean_simp(x_26, x_31, x_28, x_35, x_33, x_37, x_32, x_34, x_30);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_34);
lean_inc(x_32);
lean_inc(x_37);
lean_inc(x_33);
x_43 = l_Lean_Meta_Simp_mkCongr(x_29, x_41, x_33, x_37, x_32, x_34, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_box(0);
x_47 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2___lam__0(x_27, x_44, x_46, x_31, x_28, x_35, x_33, x_37, x_32, x_34, x_45);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_35);
lean_dec(x_28);
lean_dec(x_31);
lean_dec(x_27);
x_15 = x_47;
goto block_23;
}
else
{
uint8_t x_48; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
return x_43;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_43, 0);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_43);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_52 = !lean_is_exclusive(x_40);
if (x_52 == 0)
{
return x_40;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_40, 0);
x_54 = lean_ctor_get(x_40, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_40);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_29, 0);
lean_inc(x_56);
lean_inc(x_34);
lean_inc(x_32);
lean_inc(x_37);
lean_inc(x_33);
x_57 = lean_infer_type(x_56, x_33, x_37, x_32, x_34, x_30);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_34);
lean_inc(x_32);
lean_inc(x_37);
x_60 = l_Lean_Meta_whnfD(x_58, x_33, x_37, x_32, x_34, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Expr_isArrow(x_61);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; 
lean_inc(x_34);
lean_inc(x_32);
lean_inc(x_37);
lean_inc(x_33);
lean_inc(x_35);
lean_inc(x_28);
lean_inc(x_31);
x_64 = lean_dsimp(x_26, x_31, x_28, x_35, x_33, x_37, x_32, x_34, x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_34);
lean_inc(x_32);
lean_inc(x_37);
lean_inc(x_33);
x_67 = l_Lean_Meta_Simp_mkCongrFun(x_29, x_65, x_33, x_37, x_32, x_34, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_box(0);
x_71 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2___lam__0(x_27, x_68, x_70, x_31, x_28, x_35, x_33, x_37, x_32, x_34, x_69);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_35);
lean_dec(x_28);
lean_dec(x_31);
lean_dec(x_27);
x_15 = x_71;
goto block_23;
}
else
{
uint8_t x_72; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_72 = !lean_is_exclusive(x_67);
if (x_72 == 0)
{
return x_67;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_67, 0);
x_74 = lean_ctor_get(x_67, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_67);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_76 = !lean_is_exclusive(x_64);
if (x_76 == 0)
{
return x_64;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_64, 0);
x_78 = lean_ctor_get(x_64, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_64);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; 
lean_inc(x_34);
lean_inc(x_32);
lean_inc(x_37);
lean_inc(x_33);
lean_inc(x_35);
lean_inc(x_28);
lean_inc(x_31);
x_80 = lean_simp(x_26, x_31, x_28, x_35, x_33, x_37, x_32, x_34, x_62);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_34);
lean_inc(x_32);
lean_inc(x_37);
lean_inc(x_33);
x_83 = l_Lean_Meta_Simp_mkCongr(x_29, x_81, x_33, x_37, x_32, x_34, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_box(0);
x_87 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2___lam__0(x_27, x_84, x_86, x_31, x_28, x_35, x_33, x_37, x_32, x_34, x_85);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_35);
lean_dec(x_28);
lean_dec(x_31);
lean_dec(x_27);
x_15 = x_87;
goto block_23;
}
else
{
uint8_t x_88; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_88 = !lean_is_exclusive(x_83);
if (x_88 == 0)
{
return x_83;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_83, 0);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_83);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_92 = !lean_is_exclusive(x_80);
if (x_92 == 0)
{
return x_80;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_80, 0);
x_94 = lean_ctor_get(x_80, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_80);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_96 = !lean_is_exclusive(x_60);
if (x_96 == 0)
{
return x_60;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_60, 0);
x_98 = lean_ctor_get(x_60, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_60);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_100 = !lean_is_exclusive(x_57);
if (x_100 == 0)
{
return x_57;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_57, 0);
x_102 = lean_ctor_get(x_57, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_57);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
else
{
lean_object* x_104; 
lean_dec(x_36);
lean_inc(x_34);
lean_inc(x_32);
lean_inc(x_37);
lean_inc(x_33);
x_104 = l_Lean_Meta_Simp_mkCongrFun(x_29, x_26, x_33, x_37, x_32, x_34, x_30);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_box(0);
x_108 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2___lam__0(x_27, x_105, x_107, x_31, x_28, x_35, x_33, x_37, x_32, x_34, x_106);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_35);
lean_dec(x_28);
lean_dec(x_31);
lean_dec(x_27);
x_15 = x_108;
goto block_23;
}
else
{
uint8_t x_109; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_109 = !lean_is_exclusive(x_104);
if (x_109 == 0)
{
return x_104;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_104, 0);
x_111 = lean_ctor_get(x_104, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_104);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
block_126:
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_array_fget(x_1, x_27);
x_124 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 14);
if (x_124 == 0)
{
x_28 = x_116;
x_29 = x_114;
x_30 = x_122;
x_31 = x_115;
x_32 = x_120;
x_33 = x_118;
x_34 = x_121;
x_35 = x_117;
x_36 = x_123;
x_37 = x_119;
x_38 = x_124;
goto block_113;
}
else
{
uint8_t x_125; 
x_125 = l_Lean_Meta_ParamInfo_isInstImplicit(x_123);
x_28 = x_116;
x_29 = x_114;
x_30 = x_122;
x_31 = x_115;
x_32 = x_120;
x_33 = x_118;
x_34 = x_121;
x_35 = x_117;
x_36 = x_123;
x_37 = x_119;
x_38 = x_125;
goto block_113;
}
}
}
block_23:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_add(x_5, x_20);
x_22 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2(x_1, x_2, x_3, x_4, x_21, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_congrArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Array_isEmpty___redArg(x_2);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Meta_Simp_getConfig___redArg(x_4, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_array_get_size(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Meta_getFunInfoNArgs(x_16, x_17, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set(x_12, 0, x_22);
x_23 = lean_array_size(x_2);
x_24 = lean_usize_of_nat(x_22);
x_25 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2(x_21, x_14, x_2, x_23, x_24, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_14);
lean_dec(x_21);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
return x_25;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_25, 0);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_25);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_12);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
return x_18;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_18);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
x_44 = lean_array_get_size(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_45 = l_Lean_Meta_getFunInfoNArgs(x_43, x_44, x_6, x_7, x_8, x_9, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_1);
x_51 = lean_array_size(x_2);
x_52 = lean_usize_of_nat(x_49);
x_53 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2(x_48, x_41, x_2, x_51, x_52, x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_47);
lean_dec(x_41);
lean_dec(x_48);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_61 = x_53;
} else {
 lean_dec_ref(x_53);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_63 = lean_ctor_get(x_45, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_45, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_65 = x_45;
} else {
 lean_dec_ref(x_45);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
lean_object* x_67; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_10);
return x_67;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2_spec__2(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_congrArgs_spec__2(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_congrArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_congrArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_Simp_mkCongrSimp_x3f_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_5 = lean_box(1);
x_13 = lean_array_uget(x_1, x_2);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
x_15 = lean_box(x_14);
switch (lean_obj_tag(x_15)) {
case 0:
{
x_6 = x_4;
goto block_12;
}
case 2:
{
x_6 = x_4;
goto block_12;
}
default: 
{
uint8_t x_16; 
lean_dec(x_15);
x_16 = lean_unbox(x_5);
return x_16;
}
}
block_12:
{
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = lean_unbox(x_5);
return x_11;
}
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Meta_Simp_mkCongrSimp_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_is_matcher(x_7, x_1);
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_is_matcher(x_12, x_1);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Meta_Simp_mkCongrSimp_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_isMatcher___at___Lean_Meta_Simp_mkCongrSimp_x3f_spec__1___redArg(x_1, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_196; 
x_196 = l_Lean_Expr_isConst(x_1);
if (x_196 == 0)
{
x_30 = x_4;
x_31 = x_5;
x_32 = x_6;
x_33 = x_7;
x_34 = x_8;
x_35 = x_9;
goto block_195;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_197 = l_Lean_Expr_constName_x21(x_1);
x_198 = l_Lean_Meta_isMatcher___at___Lean_Meta_Simp_mkCongrSimp_x3f_spec__1___redArg(x_197, x_8, x_9);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_unbox(x_199);
lean_dec(x_199);
if (x_200 == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
lean_dec(x_198);
x_30 = x_4;
x_31 = x_5;
x_32 = x_6;
x_33 = x_7;
x_34 = x_8;
x_35 = x_201;
goto block_195;
}
else
{
uint8_t x_202; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_202 = !lean_is_exclusive(x_198);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_198, 0);
lean_dec(x_203);
x_204 = lean_box(0);
lean_ctor_set(x_198, 0, x_204);
return x_198;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_198, 1);
lean_inc(x_205);
lean_dec(x_198);
x_206 = lean_box(0);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
block_29:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_17, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_17, 4);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_21);
lean_ctor_set(x_23, 4, x_22);
x_24 = lean_st_ref_set(x_18, x_23, x_14);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_16);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
block_195:
{
lean_object* x_36; 
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_1);
x_36 = l_Lean_Meta_getFunInfo(x_1, x_31, x_32, x_33, x_34, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_1);
x_39 = l_Lean_Meta_getCongrSimpKinds(x_1, x_37, x_31, x_32, x_33, x_34, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_array_get_size(x_40);
x_44 = lean_nat_dec_lt(x_42, x_43);
if (x_44 == 0)
{
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
x_10 = x_41;
goto block_13;
}
else
{
if (x_44 == 0)
{
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
x_10 = x_41;
goto block_13;
}
else
{
size_t x_45; size_t x_46; uint8_t x_47; 
x_45 = lean_usize_of_nat(x_42);
x_46 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_47 = l_Array_anyMUnsafe_any___at___Lean_Meta_Simp_mkCongrSimp_x3f_spec__0(x_40, x_45, x_46);
if (x_47 == 0)
{
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
x_10 = x_41;
goto block_13;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_st_ref_get(x_30, x_41);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint64_t x_56; lean_object* x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; lean_object* x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; size_t x_65; size_t x_66; lean_object* x_67; size_t x_68; size_t x_69; size_t x_70; lean_object* x_71; lean_object* x_72; 
x_52 = lean_ctor_get(x_48, 1);
x_53 = lean_ctor_get(x_48, 0);
lean_dec(x_53);
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_array_get_size(x_54);
x_56 = l_Lean_Expr_hash(x_1);
x_57 = lean_unsigned_to_nat(32u);
x_58 = lean_uint64_of_nat(x_57);
x_59 = lean_uint64_shift_right(x_56, x_58);
x_60 = lean_uint64_xor(x_56, x_59);
x_61 = lean_unsigned_to_nat(16u);
x_62 = lean_uint64_of_nat(x_61);
x_63 = lean_uint64_shift_right(x_60, x_62);
x_64 = lean_uint64_xor(x_60, x_63);
x_65 = lean_uint64_to_usize(x_64);
x_66 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_usize_of_nat(x_67);
x_69 = lean_usize_sub(x_66, x_68);
x_70 = lean_usize_land(x_65, x_69);
x_71 = lean_array_uget(x_54, x_70);
lean_dec(x_54);
x_72 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0(lean_box(0), x_1, x_71);
lean_dec(x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
lean_free_object(x_48);
lean_inc(x_1);
x_73 = l_Lean_Meta_mkCongrSimpCore_x3f(x_1, x_37, x_40, x_47, x_31, x_32, x_33, x_34, x_52);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_st_ref_take(x_30, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = !lean_is_exclusive(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; size_t x_85; size_t x_86; size_t x_87; lean_object* x_88; uint8_t x_89; 
x_81 = lean_ctor_get(x_78, 0);
x_82 = lean_ctor_get(x_78, 1);
x_83 = lean_ctor_get(x_77, 0);
lean_inc(x_83);
x_84 = lean_array_get_size(x_82);
x_85 = lean_usize_of_nat(x_84);
lean_dec(x_84);
x_86 = lean_usize_sub(x_85, x_68);
x_87 = lean_usize_land(x_65, x_86);
x_88 = lean_array_uget(x_82, x_87);
x_89 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelMVars_visitExpr_spec__0___redArg(x_1, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_90 = lean_nat_add(x_81, x_67);
lean_dec(x_81);
lean_inc(x_74);
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_1);
lean_ctor_set(x_91, 1, x_74);
lean_ctor_set(x_91, 2, x_88);
x_92 = lean_array_uset(x_82, x_87, x_91);
x_93 = lean_unsigned_to_nat(2u);
x_94 = lean_nat_shiftl(x_90, x_93);
x_95 = lean_unsigned_to_nat(3u);
x_96 = lean_nat_div(x_94, x_95);
lean_dec(x_94);
x_97 = lean_array_get_size(x_92);
x_98 = lean_nat_dec_le(x_96, x_97);
lean_dec(x_97);
lean_dec(x_96);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelMVars_visitExpr_spec__1___redArg(x_92);
lean_ctor_set(x_78, 1, x_99);
lean_ctor_set(x_78, 0, x_90);
x_14 = x_79;
x_15 = x_83;
x_16 = x_74;
x_17 = x_77;
x_18 = x_30;
x_19 = x_78;
goto block_29;
}
else
{
lean_ctor_set(x_78, 1, x_92);
lean_ctor_set(x_78, 0, x_90);
x_14 = x_79;
x_15 = x_83;
x_16 = x_74;
x_17 = x_77;
x_18 = x_30;
x_19 = x_78;
goto block_29;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_box(0);
x_101 = lean_array_uset(x_82, x_87, x_100);
lean_inc(x_74);
x_102 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_1, x_74, x_88);
x_103 = lean_array_uset(x_101, x_87, x_102);
lean_ctor_set(x_78, 1, x_103);
x_14 = x_79;
x_15 = x_83;
x_16 = x_74;
x_17 = x_77;
x_18 = x_30;
x_19 = x_78;
goto block_29;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; size_t x_108; size_t x_109; size_t x_110; lean_object* x_111; uint8_t x_112; 
x_104 = lean_ctor_get(x_78, 0);
x_105 = lean_ctor_get(x_78, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_78);
x_106 = lean_ctor_get(x_77, 0);
lean_inc(x_106);
x_107 = lean_array_get_size(x_105);
x_108 = lean_usize_of_nat(x_107);
lean_dec(x_107);
x_109 = lean_usize_sub(x_108, x_68);
x_110 = lean_usize_land(x_65, x_109);
x_111 = lean_array_uget(x_105, x_110);
x_112 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelMVars_visitExpr_spec__0___redArg(x_1, x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_113 = lean_nat_add(x_104, x_67);
lean_dec(x_104);
lean_inc(x_74);
x_114 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_114, 0, x_1);
lean_ctor_set(x_114, 1, x_74);
lean_ctor_set(x_114, 2, x_111);
x_115 = lean_array_uset(x_105, x_110, x_114);
x_116 = lean_unsigned_to_nat(2u);
x_117 = lean_nat_shiftl(x_113, x_116);
x_118 = lean_unsigned_to_nat(3u);
x_119 = lean_nat_div(x_117, x_118);
lean_dec(x_117);
x_120 = lean_array_get_size(x_115);
x_121 = lean_nat_dec_le(x_119, x_120);
lean_dec(x_120);
lean_dec(x_119);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelMVars_visitExpr_spec__1___redArg(x_115);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_113);
lean_ctor_set(x_123, 1, x_122);
x_14 = x_79;
x_15 = x_106;
x_16 = x_74;
x_17 = x_77;
x_18 = x_30;
x_19 = x_123;
goto block_29;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_113);
lean_ctor_set(x_124, 1, x_115);
x_14 = x_79;
x_15 = x_106;
x_16 = x_74;
x_17 = x_77;
x_18 = x_30;
x_19 = x_124;
goto block_29;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_box(0);
x_126 = lean_array_uset(x_105, x_110, x_125);
lean_inc(x_74);
x_127 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_1, x_74, x_111);
x_128 = lean_array_uset(x_126, x_110, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_104);
lean_ctor_set(x_129, 1, x_128);
x_14 = x_79;
x_15 = x_106;
x_16 = x_74;
x_17 = x_77;
x_18 = x_30;
x_19 = x_129;
goto block_29;
}
}
}
else
{
lean_dec(x_1);
return x_73;
}
}
else
{
lean_object* x_130; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
x_130 = lean_ctor_get(x_72, 0);
lean_inc(x_130);
lean_dec(x_72);
lean_ctor_set(x_48, 0, x_130);
return x_48;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; uint64_t x_134; lean_object* x_135; uint64_t x_136; uint64_t x_137; uint64_t x_138; lean_object* x_139; uint64_t x_140; uint64_t x_141; uint64_t x_142; size_t x_143; size_t x_144; lean_object* x_145; size_t x_146; size_t x_147; size_t x_148; lean_object* x_149; lean_object* x_150; 
x_131 = lean_ctor_get(x_48, 1);
lean_inc(x_131);
lean_dec(x_48);
x_132 = lean_ctor_get(x_50, 1);
lean_inc(x_132);
lean_dec(x_50);
x_133 = lean_array_get_size(x_132);
x_134 = l_Lean_Expr_hash(x_1);
x_135 = lean_unsigned_to_nat(32u);
x_136 = lean_uint64_of_nat(x_135);
x_137 = lean_uint64_shift_right(x_134, x_136);
x_138 = lean_uint64_xor(x_134, x_137);
x_139 = lean_unsigned_to_nat(16u);
x_140 = lean_uint64_of_nat(x_139);
x_141 = lean_uint64_shift_right(x_138, x_140);
x_142 = lean_uint64_xor(x_138, x_141);
x_143 = lean_uint64_to_usize(x_142);
x_144 = lean_usize_of_nat(x_133);
lean_dec(x_133);
x_145 = lean_unsigned_to_nat(1u);
x_146 = lean_usize_of_nat(x_145);
x_147 = lean_usize_sub(x_144, x_146);
x_148 = lean_usize_land(x_143, x_147);
x_149 = lean_array_uget(x_132, x_148);
lean_dec(x_132);
x_150 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_SynthInstance_findEntry_x3f_spec__0(lean_box(0), x_1, x_149);
lean_dec(x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
lean_inc(x_1);
x_151 = l_Lean_Meta_mkCongrSimpCore_x3f(x_1, x_37, x_40, x_47, x_31, x_32, x_33, x_34, x_131);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; size_t x_163; size_t x_164; size_t x_165; lean_object* x_166; uint8_t x_167; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_st_ref_take(x_30, x_153);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
lean_dec(x_154);
x_158 = lean_ctor_get(x_156, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_160 = x_156;
} else {
 lean_dec_ref(x_156);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_155, 0);
lean_inc(x_161);
x_162 = lean_array_get_size(x_159);
x_163 = lean_usize_of_nat(x_162);
lean_dec(x_162);
x_164 = lean_usize_sub(x_163, x_146);
x_165 = lean_usize_land(x_143, x_164);
x_166 = lean_array_uget(x_159, x_165);
x_167 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelMVars_visitExpr_spec__0___redArg(x_1, x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_168 = lean_nat_add(x_158, x_145);
lean_dec(x_158);
lean_inc(x_152);
x_169 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_169, 0, x_1);
lean_ctor_set(x_169, 1, x_152);
lean_ctor_set(x_169, 2, x_166);
x_170 = lean_array_uset(x_159, x_165, x_169);
x_171 = lean_unsigned_to_nat(2u);
x_172 = lean_nat_shiftl(x_168, x_171);
x_173 = lean_unsigned_to_nat(3u);
x_174 = lean_nat_div(x_172, x_173);
lean_dec(x_172);
x_175 = lean_array_get_size(x_170);
x_176 = lean_nat_dec_le(x_174, x_175);
lean_dec(x_175);
lean_dec(x_174);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelMVars_visitExpr_spec__1___redArg(x_170);
if (lean_is_scalar(x_160)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_160;
}
lean_ctor_set(x_178, 0, x_168);
lean_ctor_set(x_178, 1, x_177);
x_14 = x_157;
x_15 = x_161;
x_16 = x_152;
x_17 = x_155;
x_18 = x_30;
x_19 = x_178;
goto block_29;
}
else
{
lean_object* x_179; 
if (lean_is_scalar(x_160)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_160;
}
lean_ctor_set(x_179, 0, x_168);
lean_ctor_set(x_179, 1, x_170);
x_14 = x_157;
x_15 = x_161;
x_16 = x_152;
x_17 = x_155;
x_18 = x_30;
x_19 = x_179;
goto block_29;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_180 = lean_box(0);
x_181 = lean_array_uset(x_159, x_165, x_180);
lean_inc(x_152);
x_182 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_SynthInstance_newSubgoal_spec__0___redArg(x_1, x_152, x_166);
x_183 = lean_array_uset(x_181, x_165, x_182);
if (lean_is_scalar(x_160)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_160;
}
lean_ctor_set(x_184, 0, x_158);
lean_ctor_set(x_184, 1, x_183);
x_14 = x_157;
x_15 = x_161;
x_16 = x_152;
x_17 = x_155;
x_18 = x_30;
x_19 = x_184;
goto block_29;
}
}
else
{
lean_dec(x_1);
return x_151;
}
}
else
{
lean_object* x_185; lean_object* x_186; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
x_185 = lean_ctor_get(x_150, 0);
lean_inc(x_185);
lean_dec(x_150);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_131);
return x_186;
}
}
}
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
x_187 = !lean_is_exclusive(x_39);
if (x_187 == 0)
{
return x_39;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_39, 0);
x_189 = lean_ctor_get(x_39, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_39);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
x_191 = !lean_is_exclusive(x_36);
if (x_191 == 0)
{
return x_36;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_36, 0);
x_193 = lean_ctor_get(x_36, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_36);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_Simp_mkCongrSimp_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___Lean_Meta_Simp_mkCongrSimp_x3f_spec__0(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Meta_Simp_mkCongrSimp_x3f_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isMatcher___at___Lean_Meta_Simp_mkCongrSimp_x3f_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Meta_Simp_mkCongrSimp_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_isMatcher___at___Lean_Meta_Simp_mkCongrSimp_x3f_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkCongrSimp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_mkCongrSimp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_14 = l_instMonadEIO(lean_box(0));
x_15 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_17);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_27, 0, lean_box(0));
lean_closure_set(x_27, 1, lean_box(0));
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_29, 0, x_28);
lean_inc(x_29);
lean_inc(x_26);
lean_inc(x_23);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_12);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_13);
x_32 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_34);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_38, 0, x_23);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_26);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_29);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_10);
lean_ctor_set(x_44, 2, x_39);
lean_ctor_set(x_44, 3, x_41);
lean_ctor_set(x_44, 4, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_11);
x_46 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_45);
x_47 = lean_box(0);
x_48 = l_instInhabitedOfMonad___redArg(x_46, x_47);
x_49 = lean_alloc_closure((void*)(l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_49, 0, x_48);
x_50 = lean_alloc_closure((void*)(l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0___lam__1___boxed), 2, 1);
lean_closure_set(x_50, 0, x_49);
x_51 = lean_panic_fn(x_50, x_1);
x_52 = lean_apply_8(x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_52;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_nat_add(x_7, x_1);
x_19 = lean_box(x_8);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(x_6);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_box(x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_17);
return x_29;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_23; uint8_t x_28; 
x_28 = lean_usize_dec_lt(x_6, x_5);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_15);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_30 = lean_ctor_get(x_7, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_7, 1);
lean_inc(x_31);
lean_dec(x_7);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_30, 2);
lean_inc(x_43);
x_44 = lean_nat_dec_lt(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_41);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_34);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_32);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_30);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_15);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_154; 
x_52 = lean_array_uget(x_4, x_6);
x_53 = lean_ctor_get(x_30, 0);
lean_inc(x_53);
lean_dec(x_30);
x_54 = lean_array_fget(x_53, x_42);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_42, x_56);
lean_dec(x_42);
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_58, 2, x_43);
x_154 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 14);
if (x_154 == 0)
{
uint8_t x_155; uint8_t x_156; uint8_t x_157; 
x_155 = lean_unbox(x_36);
lean_dec(x_36);
x_156 = lean_unbox(x_38);
lean_dec(x_38);
x_157 = lean_unbox(x_41);
lean_dec(x_41);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_99 = x_32;
x_100 = x_34;
x_101 = x_155;
x_102 = x_156;
x_103 = x_40;
x_104 = x_157;
x_105 = x_8;
x_106 = x_9;
x_107 = x_10;
x_108 = x_11;
x_109 = x_12;
x_110 = x_13;
x_111 = x_14;
x_112 = x_15;
goto block_153;
}
else
{
lean_object* x_158; uint8_t x_159; 
x_158 = lean_array_get_size(x_3);
x_159 = lean_nat_dec_lt(x_40, x_158);
lean_dec(x_158);
if (x_159 == 0)
{
uint8_t x_160; uint8_t x_161; uint8_t x_162; 
x_160 = lean_unbox(x_36);
lean_dec(x_36);
x_161 = lean_unbox(x_38);
lean_dec(x_38);
x_162 = lean_unbox(x_41);
lean_dec(x_41);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_99 = x_32;
x_100 = x_34;
x_101 = x_160;
x_102 = x_161;
x_103 = x_40;
x_104 = x_162;
x_105 = x_8;
x_106 = x_9;
x_107 = x_10;
x_108 = x_11;
x_109 = x_12;
x_110 = x_13;
x_111 = x_14;
x_112 = x_15;
goto block_153;
}
else
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_array_fget(x_3, x_40);
x_164 = l_Lean_Meta_ParamInfo_isInstImplicit(x_163);
lean_dec(x_163);
if (x_164 == 0)
{
uint8_t x_165; uint8_t x_166; uint8_t x_167; 
x_165 = lean_unbox(x_36);
lean_dec(x_36);
x_166 = lean_unbox(x_38);
lean_dec(x_38);
x_167 = lean_unbox(x_41);
lean_dec(x_41);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_99 = x_32;
x_100 = x_34;
x_101 = x_165;
x_102 = x_166;
x_103 = x_40;
x_104 = x_167;
x_105 = x_8;
x_106 = x_9;
x_107 = x_10;
x_108 = x_11;
x_109 = x_12;
x_110 = x_13;
x_111 = x_14;
x_112 = x_15;
goto block_153;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_168 = lean_array_push(x_34, x_52);
x_169 = lean_nat_add(x_40, x_56);
lean_dec(x_40);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_41);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_38);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_36);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_168);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_32);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_58);
lean_ctor_set(x_175, 1, x_174);
x_16 = x_175;
x_17 = x_15;
goto block_22;
}
}
}
block_79:
{
uint8_t x_74; 
x_74 = lean_expr_eqv(x_52, x_62);
lean_dec(x_62);
lean_dec(x_52);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_box(0);
x_76 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___lam__0(x_56, x_58, x_61, x_59, x_60, x_64, x_63, x_1, x_75, x_66, x_67, x_68, x_69, x_70, x_71, x_72, x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_63);
x_23 = x_76;
goto block_27;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_box(0);
x_78 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___lam__0(x_56, x_58, x_61, x_59, x_60, x_64, x_63, x_65, x_77, x_66, x_67, x_68, x_69, x_70, x_71, x_72, x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_63);
x_23 = x_78;
goto block_27;
}
}
block_98:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_array_push(x_85, x_82);
x_96 = lean_box(0);
x_97 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___lam__0(x_56, x_58, x_83, x_95, x_80, x_81, x_84, x_86, x_96, x_87, x_88, x_89, x_90, x_91, x_92, x_93, x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_84);
x_23 = x_97;
goto block_27;
}
block_153:
{
lean_object* x_113; 
x_113 = lean_box(x_55);
switch (lean_obj_tag(x_113)) {
case 0:
{
lean_object* x_114; 
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_52);
x_114 = lean_dsimp(x_52, x_105, x_106, x_107, x_108, x_109, x_110, x_111, x_112);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_expr_eqv(x_52, x_115);
lean_dec(x_52);
if (x_117 == 0)
{
x_80 = x_101;
x_81 = x_102;
x_82 = x_115;
x_83 = x_99;
x_84 = x_103;
x_85 = x_100;
x_86 = x_1;
x_87 = x_105;
x_88 = x_106;
x_89 = x_107;
x_90 = x_108;
x_91 = x_109;
x_92 = x_110;
x_93 = x_111;
x_94 = x_116;
goto block_98;
}
else
{
x_80 = x_101;
x_81 = x_102;
x_82 = x_115;
x_83 = x_99;
x_84 = x_103;
x_85 = x_100;
x_86 = x_104;
x_87 = x_105;
x_88 = x_106;
x_89 = x_107;
x_90 = x_108;
x_91 = x_109;
x_92 = x_110;
x_93 = x_111;
x_94 = x_116;
goto block_98;
}
}
else
{
uint8_t x_118; 
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_103);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_58);
lean_dec(x_52);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_118 = !lean_is_exclusive(x_114);
if (x_118 == 0)
{
return x_114;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_114, 0);
x_120 = lean_ctor_get(x_114, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_114);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
case 2:
{
lean_object* x_122; 
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_52);
x_122 = lean_simp(x_52, x_105, x_106, x_107, x_108, x_109, x_110, x_111, x_112);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
lean_inc(x_123);
x_125 = lean_array_push(x_99, x_123);
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
lean_inc(x_126);
x_127 = lean_array_push(x_100, x_126);
x_128 = lean_ctor_get(x_123, 1);
lean_inc(x_128);
lean_dec(x_123);
if (lean_obj_tag(x_128) == 0)
{
x_59 = x_127;
x_60 = x_101;
x_61 = x_125;
x_62 = x_126;
x_63 = x_103;
x_64 = x_102;
x_65 = x_104;
x_66 = x_105;
x_67 = x_106;
x_68 = x_107;
x_69 = x_108;
x_70 = x_109;
x_71 = x_110;
x_72 = x_111;
x_73 = x_124;
goto block_79;
}
else
{
lean_dec(x_128);
x_59 = x_127;
x_60 = x_101;
x_61 = x_125;
x_62 = x_126;
x_63 = x_103;
x_64 = x_1;
x_65 = x_104;
x_66 = x_105;
x_67 = x_106;
x_68 = x_107;
x_69 = x_108;
x_70 = x_109;
x_71 = x_110;
x_72 = x_111;
x_73 = x_124;
goto block_79;
}
}
else
{
uint8_t x_129; 
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_103);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_58);
lean_dec(x_52);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_129 = !lean_is_exclusive(x_122);
if (x_129 == 0)
{
return x_122;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_122, 0);
x_131 = lean_ctor_get(x_122, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_122);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
case 3:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_array_push(x_100, x_52);
x_134 = lean_box(0);
x_135 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___lam__0(x_56, x_58, x_99, x_133, x_1, x_102, x_103, x_104, x_134, x_105, x_106, x_107, x_108, x_109, x_110, x_111, x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_103);
x_23 = x_135;
goto block_27;
}
case 5:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_array_push(x_100, x_52);
x_137 = lean_box(0);
x_138 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___lam__0(x_56, x_58, x_99, x_136, x_101, x_102, x_103, x_104, x_137, x_105, x_106, x_107, x_108, x_109, x_110, x_111, x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_103);
x_23 = x_138;
goto block_27;
}
default: 
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_113);
lean_dec(x_52);
x_139 = lean_mk_string_unchecked("Lean.Meta.Tactic.Simp.Types", 27, 27);
x_140 = lean_mk_string_unchecked("Lean.Meta.Simp.tryAutoCongrTheorem\?", 35, 35);
x_141 = lean_unsigned_to_nat(688u);
x_142 = lean_unsigned_to_nat(11u);
x_143 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_144 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_139, x_140, x_141, x_142, x_143);
lean_dec(x_143);
lean_dec(x_140);
lean_dec(x_139);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
x_145 = l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0(x_144, x_105, x_106, x_107, x_108, x_109, x_110, x_111, x_112);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___lam__0(x_56, x_58, x_99, x_100, x_101, x_102, x_103, x_104, x_146, x_105, x_106, x_107, x_108, x_109, x_110, x_111, x_147);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_146);
lean_dec(x_103);
x_23 = x_148;
goto block_27;
}
else
{
uint8_t x_149; 
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_103);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_58);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_149 = !lean_is_exclusive(x_145);
if (x_149 == 0)
{
return x_145;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_145, 0);
x_151 = lean_ctor_get(x_145, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_145);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
}
}
}
block_22:
{
lean_object* x_18; size_t x_19; size_t x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_6, x_19);
x_6 = x_20;
x_7 = x_16;
x_15 = x_17;
goto _start;
}
block_27:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_16 = x_26;
x_17 = x_25;
goto block_22;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_21; 
x_21 = lean_usize_dec_lt(x_4, x_3);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_13);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_23 = lean_box(0);
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
lean_dec(x_5);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_27, 2);
lean_inc(x_36);
x_37 = lean_nat_dec_lt(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_34);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_27);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_25);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_13);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_45 = lean_ctor_get(x_27, 0);
lean_inc(x_45);
lean_dec(x_27);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_35, x_46);
lean_inc(x_45);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_36);
x_49 = lean_ctor_get(x_25, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_25, 2);
lean_inc(x_50);
x_51 = lean_nat_dec_lt(x_49, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_45);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_33);
lean_ctor_set(x_52, 1, x_34);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_31);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_29);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_25);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_23);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_13);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_59 = lean_array_uget(x_2, x_4);
x_60 = lean_array_fget(x_45, x_35);
lean_dec(x_35);
lean_dec(x_45);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
x_62 = lean_ctor_get(x_25, 0);
lean_inc(x_62);
lean_dec(x_25);
x_63 = lean_nat_add(x_49, x_46);
lean_inc(x_62);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_50);
lean_inc(x_59);
x_80 = l_Lean_Expr_app___override(x_31, x_59);
x_81 = l_Lean_Expr_bindingBody_x21(x_34);
lean_dec(x_34);
x_82 = lean_box(x_61);
switch (lean_obj_tag(x_82)) {
case 0:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_59);
x_83 = lean_array_fget(x_62, x_49);
lean_dec(x_49);
lean_dec(x_62);
x_84 = lean_array_push(x_33, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_29);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_48);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_64);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_23);
lean_ctor_set(x_90, 1, x_89);
x_14 = x_90;
x_15 = x_13;
goto block_20;
}
case 2:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_62);
lean_dec(x_49);
x_91 = l_Lean_Meta_Simp_instInhabitedResult;
x_92 = lean_array_get(x_91, x_1, x_29);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_92);
lean_inc(x_59);
x_93 = l_Lean_Meta_Simp_Result_getProof_x27(x_59, x_92, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_array_push(x_33, x_59);
x_97 = lean_nat_add(x_29, x_46);
lean_dec(x_29);
x_98 = lean_ctor_get(x_92, 0);
lean_inc(x_98);
lean_dec(x_92);
lean_inc(x_94);
lean_inc(x_98);
x_99 = l_Lean_mkAppB(x_80, x_98, x_94);
x_100 = lean_array_push(x_96, x_98);
x_101 = lean_array_push(x_100, x_94);
x_102 = l_Lean_Expr_bindingBody_x21(x_81);
lean_dec(x_81);
x_103 = l_Lean_Expr_bindingBody_x21(x_102);
lean_dec(x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_99);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_97);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_48);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_64);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_23);
lean_ctor_set(x_109, 1, x_108);
x_14 = x_109;
x_15 = x_95;
goto block_20;
}
else
{
uint8_t x_110; 
lean_dec(x_92);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_64);
lean_dec(x_59);
lean_dec(x_48);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_110 = !lean_is_exclusive(x_93);
if (x_110 == 0)
{
return x_93;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_93, 0);
x_112 = lean_ctor_get(x_93, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_93);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
case 3:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_62);
lean_dec(x_49);
x_114 = lean_array_push(x_33, x_59);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_81);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_80);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_29);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_48);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_64);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_23);
lean_ctor_set(x_120, 1, x_119);
x_14 = x_120;
x_15 = x_13;
goto block_20;
}
case 5:
{
lean_object* x_121; 
lean_dec(x_62);
lean_dec(x_49);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_59);
x_121 = lean_infer_type(x_59, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_138; lean_object* x_139; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_124 = x_121;
} else {
 lean_dec_ref(x_121);
 x_124 = lean_box(0);
}
x_125 = l_Lean_Expr_bindingDomain_x21(x_81);
lean_inc(x_59);
x_126 = lean_array_push(x_33, x_59);
x_138 = lean_expr_instantiate_rev(x_125, x_126);
lean_dec(x_125);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_138);
x_139 = l_Lean_Meta_isExprDefEq(x_122, x_138, x_9, x_10, x_11, x_12, x_123);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_unbox(x_140);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_59);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_dec(x_139);
x_143 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_138);
x_144 = l_Lean_Meta_trySynthInstance(x_138, x_143, x_9, x_10, x_11, x_12, x_142);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
if (lean_obj_tag(x_145) == 1)
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_138);
lean_dec(x_124);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
lean_dec(x_145);
x_65 = x_80;
x_66 = x_126;
x_67 = x_81;
x_68 = x_147;
x_69 = x_146;
goto block_79;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_145);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_148 = lean_ctor_get(x_144, 1);
lean_inc(x_148);
lean_dec(x_144);
x_149 = lean_mk_string_unchecked("Meta", 4, 4);
x_150 = lean_mk_string_unchecked("Tactic", 6, 6);
x_151 = lean_mk_string_unchecked("simp", 4, 4);
x_152 = lean_mk_string_unchecked("congr", 5, 5);
x_153 = l_Lean_Name_mkStr4(x_149, x_150, x_151, x_152);
lean_inc(x_153);
x_154 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_153, x_11, x_148);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_unbox(x_155);
lean_dec(x_155);
if (x_156 == 0)
{
lean_object* x_157; 
lean_dec(x_153);
lean_dec(x_138);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
lean_dec(x_154);
x_127 = x_157;
goto block_137;
}
else
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_154);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_159 = lean_ctor_get(x_154, 1);
x_160 = lean_ctor_get(x_154, 0);
lean_dec(x_160);
x_161 = lean_mk_string_unchecked("failed to synthesize instance", 29, 29);
x_162 = l_Lean_stringToMessageData(x_161);
lean_dec(x_161);
x_163 = l_Lean_indentExpr(x_138);
lean_ctor_set_tag(x_154, 7);
lean_ctor_set(x_154, 1, x_163);
lean_ctor_set(x_154, 0, x_162);
x_164 = lean_mk_string_unchecked("", 0, 0);
x_165 = l_Lean_stringToMessageData(x_164);
lean_dec(x_164);
x_166 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_166, 0, x_154);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_153, x_166, x_9, x_10, x_11, x_12, x_159);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_127 = x_168;
goto block_137;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_169 = lean_ctor_get(x_154, 1);
lean_inc(x_169);
lean_dec(x_154);
x_170 = lean_mk_string_unchecked("failed to synthesize instance", 29, 29);
x_171 = l_Lean_stringToMessageData(x_170);
lean_dec(x_170);
x_172 = l_Lean_indentExpr(x_138);
x_173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_mk_string_unchecked("", 0, 0);
x_175 = l_Lean_stringToMessageData(x_174);
lean_dec(x_174);
x_176 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_153, x_176, x_9, x_10, x_11, x_12, x_169);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec(x_177);
x_127 = x_178;
goto block_137;
}
}
}
}
else
{
uint8_t x_179; 
lean_dec(x_138);
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_64);
lean_dec(x_48);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_179 = !lean_is_exclusive(x_144);
if (x_179 == 0)
{
return x_144;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_144, 0);
x_181 = lean_ctor_get(x_144, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_144);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
else
{
lean_object* x_183; 
lean_dec(x_138);
lean_dec(x_124);
x_183 = lean_ctor_get(x_139, 1);
lean_inc(x_183);
lean_dec(x_139);
x_65 = x_80;
x_66 = x_126;
x_67 = x_81;
x_68 = x_59;
x_69 = x_183;
goto block_79;
}
}
else
{
uint8_t x_184; 
lean_dec(x_138);
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_64);
lean_dec(x_59);
lean_dec(x_48);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_184 = !lean_is_exclusive(x_139);
if (x_184 == 0)
{
return x_139;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_139, 0);
x_186 = lean_ctor_get(x_139, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_139);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
block_137:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_81);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_80);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_29);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_48);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_64);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_129);
lean_ctor_set(x_135, 1, x_134);
if (lean_is_scalar(x_124)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_124;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_127);
return x_136;
}
}
else
{
uint8_t x_188; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_64);
lean_dec(x_59);
lean_dec(x_48);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_188 = !lean_is_exclusive(x_121);
if (x_188 == 0)
{
return x_121;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_121, 0);
x_190 = lean_ctor_get(x_121, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_121);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
default: 
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_82);
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_49);
x_192 = lean_mk_string_unchecked("Lean.Meta.Tactic.Simp.Types", 27, 27);
x_193 = lean_mk_string_unchecked("Lean.Meta.Simp.tryAutoCongrTheorem\?", 35, 35);
x_194 = lean_unsigned_to_nat(755u);
x_195 = lean_unsigned_to_nat(11u);
x_196 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_197 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_192, x_193, x_194, x_195, x_196);
lean_dec(x_196);
lean_dec(x_193);
lean_dec(x_192);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_198 = l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0(x_197, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_33);
lean_ctor_set(x_200, 1, x_81);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_80);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_29);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_48);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_64);
lean_ctor_set(x_204, 1, x_203);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_23);
lean_ctor_set(x_205, 1, x_204);
x_14 = x_205;
x_15 = x_199;
goto block_20;
}
else
{
uint8_t x_206; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_64);
lean_dec(x_48);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_206 = !lean_is_exclusive(x_198);
if (x_206 == 0)
{
return x_198;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_198, 0);
x_208 = lean_ctor_get(x_198, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_198);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
}
block_79:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_inc(x_68);
x_70 = l_Lean_Expr_app___override(x_65, x_68);
x_71 = lean_array_push(x_66, x_68);
x_72 = l_Lean_Expr_bindingBody_x21(x_67);
lean_dec(x_67);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_29);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_48);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_23);
lean_ctor_set(x_78, 1, x_77);
x_14 = x_78;
x_15 = x_69;
goto block_20;
}
}
}
}
block_20:
{
lean_object* x_16; size_t x_17; size_t x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_4, x_17);
x_4 = x_18;
x_5 = x_14;
x_13 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_21; 
x_21 = lean_usize_dec_lt(x_4, x_3);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_13);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_23 = lean_box(0);
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
lean_dec(x_5);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_27, 2);
lean_inc(x_36);
x_37 = lean_nat_dec_lt(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_34);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_27);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_25);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_13);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_45 = lean_ctor_get(x_27, 0);
lean_inc(x_45);
lean_dec(x_27);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_35, x_46);
lean_inc(x_45);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_36);
x_49 = lean_ctor_get(x_25, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_25, 2);
lean_inc(x_50);
x_51 = lean_nat_dec_lt(x_49, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_45);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_33);
lean_ctor_set(x_52, 1, x_34);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_31);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_29);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_25);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_23);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_13);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_59 = lean_array_uget(x_2, x_4);
x_60 = lean_array_fget(x_45, x_35);
lean_dec(x_35);
lean_dec(x_45);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
x_62 = lean_ctor_get(x_25, 0);
lean_inc(x_62);
lean_dec(x_25);
x_63 = lean_nat_add(x_49, x_46);
lean_inc(x_62);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_50);
lean_inc(x_59);
x_80 = l_Lean_Expr_app___override(x_31, x_59);
x_81 = l_Lean_Expr_bindingBody_x21(x_34);
lean_dec(x_34);
x_82 = lean_box(x_61);
switch (lean_obj_tag(x_82)) {
case 0:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_59);
x_83 = lean_array_fget(x_62, x_49);
lean_dec(x_49);
lean_dec(x_62);
x_84 = lean_array_push(x_33, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_29);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_48);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_64);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_23);
lean_ctor_set(x_90, 1, x_89);
x_14 = x_90;
x_15 = x_13;
goto block_20;
}
case 2:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_62);
lean_dec(x_49);
x_91 = l_Lean_Meta_Simp_instInhabitedResult;
x_92 = lean_array_get(x_91, x_1, x_29);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_92);
lean_inc(x_59);
x_93 = l_Lean_Meta_Simp_Result_getProof_x27(x_59, x_92, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_array_push(x_33, x_59);
x_97 = lean_nat_add(x_29, x_46);
lean_dec(x_29);
x_98 = lean_ctor_get(x_92, 0);
lean_inc(x_98);
lean_dec(x_92);
lean_inc(x_94);
lean_inc(x_98);
x_99 = l_Lean_mkAppB(x_80, x_98, x_94);
x_100 = lean_array_push(x_96, x_98);
x_101 = lean_array_push(x_100, x_94);
x_102 = l_Lean_Expr_bindingBody_x21(x_81);
lean_dec(x_81);
x_103 = l_Lean_Expr_bindingBody_x21(x_102);
lean_dec(x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_99);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_97);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_48);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_64);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_23);
lean_ctor_set(x_109, 1, x_108);
x_14 = x_109;
x_15 = x_95;
goto block_20;
}
else
{
uint8_t x_110; 
lean_dec(x_92);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_64);
lean_dec(x_59);
lean_dec(x_48);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_110 = !lean_is_exclusive(x_93);
if (x_110 == 0)
{
return x_93;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_93, 0);
x_112 = lean_ctor_get(x_93, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_93);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
case 3:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_62);
lean_dec(x_49);
x_114 = lean_array_push(x_33, x_59);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_81);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_80);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_29);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_48);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_64);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_23);
lean_ctor_set(x_120, 1, x_119);
x_14 = x_120;
x_15 = x_13;
goto block_20;
}
case 5:
{
lean_object* x_121; 
lean_dec(x_62);
lean_dec(x_49);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_59);
x_121 = lean_infer_type(x_59, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_138; lean_object* x_139; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_124 = x_121;
} else {
 lean_dec_ref(x_121);
 x_124 = lean_box(0);
}
x_125 = l_Lean_Expr_bindingDomain_x21(x_81);
lean_inc(x_59);
x_126 = lean_array_push(x_33, x_59);
x_138 = lean_expr_instantiate_rev(x_125, x_126);
lean_dec(x_125);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_138);
x_139 = l_Lean_Meta_isExprDefEq(x_122, x_138, x_9, x_10, x_11, x_12, x_123);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_unbox(x_140);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_59);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_dec(x_139);
x_143 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_138);
x_144 = l_Lean_Meta_trySynthInstance(x_138, x_143, x_9, x_10, x_11, x_12, x_142);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
if (lean_obj_tag(x_145) == 1)
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_138);
lean_dec(x_124);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
lean_dec(x_145);
x_65 = x_80;
x_66 = x_126;
x_67 = x_81;
x_68 = x_147;
x_69 = x_146;
goto block_79;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_145);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_148 = lean_ctor_get(x_144, 1);
lean_inc(x_148);
lean_dec(x_144);
x_149 = lean_mk_string_unchecked("Meta", 4, 4);
x_150 = lean_mk_string_unchecked("Tactic", 6, 6);
x_151 = lean_mk_string_unchecked("simp", 4, 4);
x_152 = lean_mk_string_unchecked("congr", 5, 5);
x_153 = l_Lean_Name_mkStr4(x_149, x_150, x_151, x_152);
lean_inc(x_153);
x_154 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_153, x_11, x_148);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_unbox(x_155);
lean_dec(x_155);
if (x_156 == 0)
{
lean_object* x_157; 
lean_dec(x_153);
lean_dec(x_138);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
lean_dec(x_154);
x_127 = x_157;
goto block_137;
}
else
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_154);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_159 = lean_ctor_get(x_154, 1);
x_160 = lean_ctor_get(x_154, 0);
lean_dec(x_160);
x_161 = lean_mk_string_unchecked("failed to synthesize instance", 29, 29);
x_162 = l_Lean_stringToMessageData(x_161);
lean_dec(x_161);
x_163 = l_Lean_indentExpr(x_138);
lean_ctor_set_tag(x_154, 7);
lean_ctor_set(x_154, 1, x_163);
lean_ctor_set(x_154, 0, x_162);
x_164 = lean_mk_string_unchecked("", 0, 0);
x_165 = l_Lean_stringToMessageData(x_164);
lean_dec(x_164);
x_166 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_166, 0, x_154);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_153, x_166, x_9, x_10, x_11, x_12, x_159);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_127 = x_168;
goto block_137;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_169 = lean_ctor_get(x_154, 1);
lean_inc(x_169);
lean_dec(x_154);
x_170 = lean_mk_string_unchecked("failed to synthesize instance", 29, 29);
x_171 = l_Lean_stringToMessageData(x_170);
lean_dec(x_170);
x_172 = l_Lean_indentExpr(x_138);
x_173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_mk_string_unchecked("", 0, 0);
x_175 = l_Lean_stringToMessageData(x_174);
lean_dec(x_174);
x_176 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_153, x_176, x_9, x_10, x_11, x_12, x_169);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec(x_177);
x_127 = x_178;
goto block_137;
}
}
}
}
else
{
uint8_t x_179; 
lean_dec(x_138);
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_64);
lean_dec(x_48);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_179 = !lean_is_exclusive(x_144);
if (x_179 == 0)
{
return x_144;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_144, 0);
x_181 = lean_ctor_get(x_144, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_144);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
else
{
lean_object* x_183; 
lean_dec(x_138);
lean_dec(x_124);
x_183 = lean_ctor_get(x_139, 1);
lean_inc(x_183);
lean_dec(x_139);
x_65 = x_80;
x_66 = x_126;
x_67 = x_81;
x_68 = x_59;
x_69 = x_183;
goto block_79;
}
}
else
{
uint8_t x_184; 
lean_dec(x_138);
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_64);
lean_dec(x_59);
lean_dec(x_48);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_184 = !lean_is_exclusive(x_139);
if (x_184 == 0)
{
return x_139;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_139, 0);
x_186 = lean_ctor_get(x_139, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_139);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
block_137:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_81);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_80);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_29);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_48);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_64);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_129);
lean_ctor_set(x_135, 1, x_134);
if (lean_is_scalar(x_124)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_124;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_127);
return x_136;
}
}
else
{
uint8_t x_188; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_64);
lean_dec(x_59);
lean_dec(x_48);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_188 = !lean_is_exclusive(x_121);
if (x_188 == 0)
{
return x_121;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_121, 0);
x_190 = lean_ctor_get(x_121, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_121);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
default: 
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_82);
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_49);
x_192 = lean_mk_string_unchecked("Lean.Meta.Tactic.Simp.Types", 27, 27);
x_193 = lean_mk_string_unchecked("Lean.Meta.Simp.tryAutoCongrTheorem\?", 35, 35);
x_194 = lean_unsigned_to_nat(755u);
x_195 = lean_unsigned_to_nat(11u);
x_196 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_197 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_192, x_193, x_194, x_195, x_196);
lean_dec(x_196);
lean_dec(x_193);
lean_dec(x_192);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_198 = l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0(x_197, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_33);
lean_ctor_set(x_200, 1, x_81);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_80);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_29);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_48);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_64);
lean_ctor_set(x_204, 1, x_203);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_23);
lean_ctor_set(x_205, 1, x_204);
x_14 = x_205;
x_15 = x_199;
goto block_20;
}
else
{
uint8_t x_206; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_64);
lean_dec(x_48);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_206 = !lean_is_exclusive(x_198);
if (x_206 == 0)
{
return x_198;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_198, 0);
x_208 = lean_ctor_get(x_198, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_198);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
}
block_79:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_inc(x_68);
x_70 = l_Lean_Expr_app___override(x_65, x_68);
x_71 = lean_array_push(x_66, x_68);
x_72 = l_Lean_Expr_bindingBody_x21(x_67);
lean_dec(x_67);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_29);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_48);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_23);
lean_ctor_set(x_78, 1, x_77);
x_14 = x_78;
x_15 = x_69;
goto block_20;
}
}
}
}
block_20:
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_4, x_17);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2_spec__2(x_1, x_2, x_3, x_18, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_15);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_14 = l_instMonadEIO(lean_box(0));
x_15 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_17);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_27, 0, lean_box(0));
lean_closure_set(x_27, 1, lean_box(0));
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_29, 0, x_28);
lean_inc(x_29);
lean_inc(x_26);
lean_inc(x_23);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_12);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_13);
x_32 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_34);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_38, 0, x_23);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_26);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_29);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_10);
lean_ctor_set(x_44, 2, x_39);
lean_ctor_set(x_44, 3, x_41);
lean_ctor_set(x_44, 4, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_11);
x_46 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_45);
x_47 = lean_box(0);
x_48 = l_instInhabitedOfMonad___redArg(x_46, x_47);
x_49 = lean_alloc_closure((void*)(l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_49, 0, x_48);
x_50 = lean_alloc_closure((void*)(l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0___lam__1___boxed), 2, 1);
lean_closure_set(x_50, 0, x_49);
x_51 = lean_panic_fn(x_50, x_1);
x_52 = lean_apply_8(x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_52;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryAutoCongrTheorem_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Expr_getAppFn(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_10);
x_11 = l_Lean_Meta_Simp_mkCongrSimp_x3f(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_20 = lean_ctor_get(x_11, 1);
x_21 = lean_ctor_get(x_11, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_23 = x_12;
} else {
 lean_dec_ref(x_12);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_22, 2);
lean_inc(x_24);
x_25 = lean_array_get_size(x_24);
x_26 = l_Lean_Expr_getAppNumArgs(x_1);
x_27 = lean_nat_dec_eq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_box(0);
lean_ctor_set(x_11, 0, x_28);
return x_11;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_free_object(x_11);
x_29 = lean_box(0);
x_30 = l_Lean_Expr_sort___override(x_29);
lean_inc(x_26);
x_31 = lean_mk_array(x_26, x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_sub(x_26, x_32);
lean_dec(x_26);
lean_inc(x_1);
x_34 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_31, x_33);
x_35 = lean_array_get_size(x_34);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_10);
x_36 = l_Lean_Meta_getFunInfoNArgs(x_10, x_35, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Meta_Simp_getConfig___redArg(x_3, x_38);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; size_t x_55; lean_object* x_56; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_box(0);
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_mk_empty_array_with_capacity(x_45);
x_47 = l_Array_toSubarray___redArg(x_24, x_45, x_25);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_43);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_49);
lean_inc(x_46);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_46);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_47);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_array_size(x_34);
x_55 = lean_usize_of_nat(x_45);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_56 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1(x_27, x_41, x_44, x_34, x_54, x_55, x_53, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_42);
lean_dec(x_44);
lean_dec(x_41);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_139; uint8_t x_140; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_64 = x_56;
} else {
 lean_dec_ref(x_56);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_58, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_66 = x_58;
} else {
 lean_dec_ref(x_58);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_60, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_68 = x_60;
} else {
 lean_dec_ref(x_60);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_61, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_70 = x_61;
} else {
 lean_dec_ref(x_61);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_62, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_62, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_73 = x_62;
} else {
 lean_dec_ref(x_62);
 x_73 = lean_box(0);
}
x_139 = lean_ctor_get(x_72, 1);
lean_inc(x_139);
lean_dec(x_72);
x_140 = lean_unbox(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_139);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_59);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_142, 0, x_1);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*2, x_27);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_39, 1, x_63);
lean_ctor_set(x_39, 0, x_143);
return x_39;
}
else
{
uint8_t x_144; 
lean_dec(x_1);
x_144 = lean_unbox(x_71);
if (x_144 == 0)
{
uint8_t x_145; 
x_145 = lean_unbox(x_69);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; 
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_59);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_146 = l_Lean_mkAppN(x_10, x_67);
lean_dec(x_67);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_unbox(x_139);
lean_dec(x_139);
lean_ctor_set_uint8(x_148, sizeof(void*)*2, x_149);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_39, 1, x_63);
lean_ctor_set(x_39, 0, x_150);
return x_39;
}
else
{
lean_dec(x_139);
lean_free_object(x_39);
lean_dec(x_10);
goto block_138;
}
}
else
{
lean_dec(x_139);
lean_free_object(x_39);
lean_dec(x_10);
goto block_138;
}
}
block_87:
{
uint8_t x_78; 
x_78 = lean_unbox(x_71);
lean_dec(x_71);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_75);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*2, x_74);
if (lean_is_scalar(x_23)) {
 x_81 = lean_alloc_ctor(1, 1, 0);
} else {
 x_81 = x_23;
}
lean_ctor_set(x_81, 0, x_80);
if (lean_is_scalar(x_64)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_64;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_77);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
if (lean_is_scalar(x_23)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_23;
}
lean_ctor_set(x_83, 0, x_75);
x_84 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_84, 0, x_76);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*2, x_74);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
if (lean_is_scalar(x_64)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_64;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_77);
return x_86;
}
}
block_138:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_88 = lean_ctor_get(x_22, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_22, 0);
lean_inc(x_89);
lean_dec(x_22);
x_90 = lean_array_get_size(x_67);
x_91 = l_Array_toSubarray___redArg(x_67, x_45, x_90);
x_92 = lean_box(0);
if (lean_is_scalar(x_73)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_73;
}
lean_ctor_set(x_93, 0, x_46);
lean_ctor_set(x_93, 1, x_89);
if (lean_is_scalar(x_70)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_70;
}
lean_ctor_set(x_94, 0, x_88);
lean_ctor_set(x_94, 1, x_93);
if (lean_is_scalar(x_68)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_68;
}
lean_ctor_set(x_95, 0, x_45);
lean_ctor_set(x_95, 1, x_94);
if (lean_is_scalar(x_66)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_66;
}
lean_ctor_set(x_96, 0, x_47);
lean_ctor_set(x_96, 1, x_95);
if (lean_is_scalar(x_59)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_59;
}
lean_ctor_set(x_97, 0, x_91);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_92);
lean_ctor_set(x_98, 1, x_97);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_99 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2(x_65, x_34, x_54, x_55, x_98, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_63);
lean_dec(x_34);
lean_dec(x_65);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_100, 0);
lean_inc(x_106);
lean_dec(x_100);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_107 = lean_ctor_get(x_99, 1);
lean_inc(x_107);
lean_dec(x_99);
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
lean_dec(x_104);
x_109 = lean_ctor_get(x_105, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
lean_dec(x_105);
x_111 = lean_expr_instantiate_rev(x_110, x_109);
lean_dec(x_109);
lean_dec(x_110);
x_112 = lean_mk_string_unchecked("Eq", 2, 2);
x_113 = l_Lean_Name_mkStr1(x_112);
x_114 = lean_unsigned_to_nat(3u);
x_115 = l_Lean_Expr_isAppOfArity(x_111, x_113, x_114);
lean_dec(x_113);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_111);
lean_dec(x_108);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_64);
lean_dec(x_23);
x_116 = lean_mk_string_unchecked("Lean.Meta.Tactic.Simp.Types", 27, 27);
x_117 = lean_mk_string_unchecked("Lean.Meta.Simp.tryAutoCongrTheorem\?", 35, 35);
x_118 = lean_unsigned_to_nat(756u);
x_119 = lean_unsigned_to_nat(61u);
x_120 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_121 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_116, x_117, x_118, x_119, x_120);
lean_dec(x_120);
lean_dec(x_117);
lean_dec(x_116);
x_122 = l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__4(x_121, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_107);
return x_122;
}
else
{
lean_object* x_123; uint8_t x_124; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = l_Lean_Expr_appArg_x21(x_111);
lean_dec(x_111);
x_124 = lean_unbox(x_69);
lean_dec(x_69);
if (x_124 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_74 = x_115;
x_75 = x_108;
x_76 = x_123;
x_77 = x_107;
goto block_87;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = l_Lean_Meta_Simp_removeUnnecessaryCasts(x_123, x_5, x_6, x_7, x_8, x_107);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_74 = x_115;
x_75 = x_108;
x_76 = x_126;
x_77 = x_127;
goto block_87;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_64);
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_128 = !lean_is_exclusive(x_99);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_99, 0);
lean_dec(x_129);
x_130 = lean_ctor_get(x_106, 0);
lean_inc(x_130);
lean_dec(x_106);
lean_ctor_set(x_99, 0, x_130);
return x_99;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_99, 1);
lean_inc(x_131);
lean_dec(x_99);
x_132 = lean_ctor_get(x_106, 0);
lean_inc(x_132);
lean_dec(x_106);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_64);
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_134 = !lean_is_exclusive(x_99);
if (x_134 == 0)
{
return x_99;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_99, 0);
x_136 = lean_ctor_get(x_99, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_99);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_47);
lean_dec(x_46);
lean_free_object(x_39);
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_56);
if (x_151 == 0)
{
return x_56;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_56, 0);
x_153 = lean_ctor_get(x_56, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_56);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; size_t x_168; size_t x_169; lean_object* x_170; 
x_155 = lean_ctor_get(x_39, 0);
x_156 = lean_ctor_get(x_39, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_39);
x_157 = lean_box(0);
x_158 = lean_ctor_get(x_37, 0);
lean_inc(x_158);
lean_dec(x_37);
x_159 = lean_unsigned_to_nat(0u);
x_160 = lean_mk_empty_array_with_capacity(x_159);
x_161 = l_Array_toSubarray___redArg(x_24, x_159, x_25);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_157);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_157);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_157);
lean_ctor_set(x_164, 1, x_163);
lean_inc(x_160);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_160);
lean_ctor_set(x_165, 1, x_164);
lean_inc(x_160);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_160);
lean_ctor_set(x_166, 1, x_165);
lean_inc(x_161);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_161);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_array_size(x_34);
x_169 = lean_usize_of_nat(x_159);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_170 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1(x_27, x_155, x_158, x_34, x_168, x_169, x_167, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_156);
lean_dec(x_158);
lean_dec(x_155);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_251; uint8_t x_252; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_173 = x_171;
} else {
 lean_dec_ref(x_171);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_170, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_178 = x_170;
} else {
 lean_dec_ref(x_170);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_172, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_180 = x_172;
} else {
 lean_dec_ref(x_172);
 x_180 = lean_box(0);
}
x_181 = lean_ctor_get(x_174, 0);
lean_inc(x_181);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_182 = x_174;
} else {
 lean_dec_ref(x_174);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_175, 0);
lean_inc(x_183);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_184 = x_175;
} else {
 lean_dec_ref(x_175);
 x_184 = lean_box(0);
}
x_185 = lean_ctor_get(x_176, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_176, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_187 = x_176;
} else {
 lean_dec_ref(x_176);
 x_187 = lean_box(0);
}
x_251 = lean_ctor_get(x_186, 1);
lean_inc(x_251);
lean_dec(x_186);
x_252 = lean_unbox(x_251);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_251);
lean_dec(x_187);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_173);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_253 = lean_box(0);
x_254 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_254, 0, x_1);
lean_ctor_set(x_254, 1, x_253);
lean_ctor_set_uint8(x_254, sizeof(void*)*2, x_27);
x_255 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_255, 0, x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_177);
return x_256;
}
else
{
uint8_t x_257; 
lean_dec(x_1);
x_257 = lean_unbox(x_185);
if (x_257 == 0)
{
uint8_t x_258; 
x_258 = lean_unbox(x_183);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_187);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_173);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_259 = l_Lean_mkAppN(x_10, x_181);
lean_dec(x_181);
x_260 = lean_box(0);
x_261 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
x_262 = lean_unbox(x_251);
lean_dec(x_251);
lean_ctor_set_uint8(x_261, sizeof(void*)*2, x_262);
x_263 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_263, 0, x_261);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_177);
return x_264;
}
else
{
lean_dec(x_251);
lean_dec(x_10);
goto block_250;
}
}
else
{
lean_dec(x_251);
lean_dec(x_10);
goto block_250;
}
}
block_201:
{
uint8_t x_192; 
x_192 = lean_unbox(x_185);
lean_dec(x_185);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_189);
x_193 = lean_box(0);
x_194 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_194, 0, x_190);
lean_ctor_set(x_194, 1, x_193);
lean_ctor_set_uint8(x_194, sizeof(void*)*2, x_188);
if (lean_is_scalar(x_23)) {
 x_195 = lean_alloc_ctor(1, 1, 0);
} else {
 x_195 = x_23;
}
lean_ctor_set(x_195, 0, x_194);
if (lean_is_scalar(x_178)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_178;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_191);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
if (lean_is_scalar(x_23)) {
 x_197 = lean_alloc_ctor(1, 1, 0);
} else {
 x_197 = x_23;
}
lean_ctor_set(x_197, 0, x_189);
x_198 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_198, 0, x_190);
lean_ctor_set(x_198, 1, x_197);
lean_ctor_set_uint8(x_198, sizeof(void*)*2, x_188);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_198);
if (lean_is_scalar(x_178)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_178;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_191);
return x_200;
}
}
block_250:
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_202 = lean_ctor_get(x_22, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_22, 0);
lean_inc(x_203);
lean_dec(x_22);
x_204 = lean_array_get_size(x_181);
x_205 = l_Array_toSubarray___redArg(x_181, x_159, x_204);
x_206 = lean_box(0);
if (lean_is_scalar(x_187)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_187;
}
lean_ctor_set(x_207, 0, x_160);
lean_ctor_set(x_207, 1, x_203);
if (lean_is_scalar(x_184)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_184;
}
lean_ctor_set(x_208, 0, x_202);
lean_ctor_set(x_208, 1, x_207);
if (lean_is_scalar(x_182)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_182;
}
lean_ctor_set(x_209, 0, x_159);
lean_ctor_set(x_209, 1, x_208);
if (lean_is_scalar(x_180)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_180;
}
lean_ctor_set(x_210, 0, x_161);
lean_ctor_set(x_210, 1, x_209);
if (lean_is_scalar(x_173)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_173;
}
lean_ctor_set(x_211, 0, x_205);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_206);
lean_ctor_set(x_212, 1, x_211);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_213 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2(x_179, x_34, x_168, x_169, x_212, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_177);
lean_dec(x_34);
lean_dec(x_179);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_dec(x_216);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
x_220 = lean_ctor_get(x_214, 0);
lean_inc(x_220);
lean_dec(x_214);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_221 = lean_ctor_get(x_213, 1);
lean_inc(x_221);
lean_dec(x_213);
x_222 = lean_ctor_get(x_218, 0);
lean_inc(x_222);
lean_dec(x_218);
x_223 = lean_ctor_get(x_219, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_219, 1);
lean_inc(x_224);
lean_dec(x_219);
x_225 = lean_expr_instantiate_rev(x_224, x_223);
lean_dec(x_223);
lean_dec(x_224);
x_226 = lean_mk_string_unchecked("Eq", 2, 2);
x_227 = l_Lean_Name_mkStr1(x_226);
x_228 = lean_unsigned_to_nat(3u);
x_229 = l_Lean_Expr_isAppOfArity(x_225, x_227, x_228);
lean_dec(x_227);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_225);
lean_dec(x_222);
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_178);
lean_dec(x_23);
x_230 = lean_mk_string_unchecked("Lean.Meta.Tactic.Simp.Types", 27, 27);
x_231 = lean_mk_string_unchecked("Lean.Meta.Simp.tryAutoCongrTheorem\?", 35, 35);
x_232 = lean_unsigned_to_nat(756u);
x_233 = lean_unsigned_to_nat(61u);
x_234 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_235 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_230, x_231, x_232, x_233, x_234);
lean_dec(x_234);
lean_dec(x_231);
lean_dec(x_230);
x_236 = l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__4(x_235, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_221);
return x_236;
}
else
{
lean_object* x_237; uint8_t x_238; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_237 = l_Lean_Expr_appArg_x21(x_225);
lean_dec(x_225);
x_238 = lean_unbox(x_183);
lean_dec(x_183);
if (x_238 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_188 = x_229;
x_189 = x_222;
x_190 = x_237;
x_191 = x_221;
goto block_201;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = l_Lean_Meta_Simp_removeUnnecessaryCasts(x_237, x_5, x_6, x_7, x_8, x_221);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_188 = x_229;
x_189 = x_222;
x_190 = x_240;
x_191 = x_241;
goto block_201;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_178);
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_242 = lean_ctor_get(x_213, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_243 = x_213;
} else {
 lean_dec_ref(x_213);
 x_243 = lean_box(0);
}
x_244 = lean_ctor_get(x_220, 0);
lean_inc(x_244);
lean_dec(x_220);
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_242);
return x_245;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_178);
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_246 = lean_ctor_get(x_213, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_213, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_248 = x_213;
} else {
 lean_dec_ref(x_213);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_265 = lean_ctor_get(x_170, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_170, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_267 = x_170;
} else {
 lean_dec_ref(x_170);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(1, 2, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_265);
lean_ctor_set(x_268, 1, x_266);
return x_268;
}
}
}
else
{
uint8_t x_269; 
lean_dec(x_34);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_269 = !lean_is_exclusive(x_36);
if (x_269 == 0)
{
return x_36;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_36, 0);
x_271 = lean_ctor_get(x_36, 1);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_36);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; 
x_273 = lean_ctor_get(x_11, 1);
lean_inc(x_273);
lean_dec(x_11);
x_274 = lean_ctor_get(x_12, 0);
lean_inc(x_274);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_275 = x_12;
} else {
 lean_dec_ref(x_12);
 x_275 = lean_box(0);
}
x_276 = lean_ctor_get(x_274, 2);
lean_inc(x_276);
x_277 = lean_array_get_size(x_276);
x_278 = l_Lean_Expr_getAppNumArgs(x_1);
x_279 = lean_nat_dec_eq(x_277, x_278);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; 
lean_dec(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_280 = lean_box(0);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_273);
return x_281;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_282 = lean_box(0);
x_283 = l_Lean_Expr_sort___override(x_282);
lean_inc(x_278);
x_284 = lean_mk_array(x_278, x_283);
x_285 = lean_unsigned_to_nat(1u);
x_286 = lean_nat_sub(x_278, x_285);
lean_dec(x_278);
lean_inc(x_1);
x_287 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_284, x_286);
x_288 = lean_array_get_size(x_287);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_10);
x_289 = l_Lean_Meta_getFunInfoNArgs(x_10, x_288, x_5, x_6, x_7, x_8, x_273);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; size_t x_307; size_t x_308; lean_object* x_309; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
lean_dec(x_289);
x_292 = l_Lean_Meta_Simp_getConfig___redArg(x_3, x_291);
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_295 = x_292;
} else {
 lean_dec_ref(x_292);
 x_295 = lean_box(0);
}
x_296 = lean_box(0);
x_297 = lean_ctor_get(x_290, 0);
lean_inc(x_297);
lean_dec(x_290);
x_298 = lean_unsigned_to_nat(0u);
x_299 = lean_mk_empty_array_with_capacity(x_298);
x_300 = l_Array_toSubarray___redArg(x_276, x_298, x_277);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_296);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_296);
lean_ctor_set(x_302, 1, x_301);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_296);
lean_ctor_set(x_303, 1, x_302);
lean_inc(x_299);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_299);
lean_ctor_set(x_304, 1, x_303);
lean_inc(x_299);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_299);
lean_ctor_set(x_305, 1, x_304);
lean_inc(x_300);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_300);
lean_ctor_set(x_306, 1, x_305);
x_307 = lean_array_size(x_287);
x_308 = lean_usize_of_nat(x_298);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_309 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1(x_279, x_293, x_297, x_287, x_307, x_308, x_306, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_294);
lean_dec(x_297);
lean_dec(x_293);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_390; uint8_t x_391; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 x_312 = x_310;
} else {
 lean_dec_ref(x_310);
 x_312 = lean_box(0);
}
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
x_315 = lean_ctor_get(x_314, 1);
lean_inc(x_315);
x_316 = lean_ctor_get(x_309, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_317 = x_309;
} else {
 lean_dec_ref(x_309);
 x_317 = lean_box(0);
}
x_318 = lean_ctor_get(x_311, 0);
lean_inc(x_318);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_319 = x_311;
} else {
 lean_dec_ref(x_311);
 x_319 = lean_box(0);
}
x_320 = lean_ctor_get(x_313, 0);
lean_inc(x_320);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_321 = x_313;
} else {
 lean_dec_ref(x_313);
 x_321 = lean_box(0);
}
x_322 = lean_ctor_get(x_314, 0);
lean_inc(x_322);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_323 = x_314;
} else {
 lean_dec_ref(x_314);
 x_323 = lean_box(0);
}
x_324 = lean_ctor_get(x_315, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_315, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_326 = x_315;
} else {
 lean_dec_ref(x_315);
 x_326 = lean_box(0);
}
x_390 = lean_ctor_get(x_325, 1);
lean_inc(x_390);
lean_dec(x_325);
x_391 = lean_unbox(x_390);
if (x_391 == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_390);
lean_dec(x_326);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_312);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_287);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_392 = lean_box(0);
x_393 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_393, 0, x_1);
lean_ctor_set(x_393, 1, x_392);
lean_ctor_set_uint8(x_393, sizeof(void*)*2, x_279);
x_394 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_394, 0, x_393);
if (lean_is_scalar(x_295)) {
 x_395 = lean_alloc_ctor(0, 2, 0);
} else {
 x_395 = x_295;
}
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_316);
return x_395;
}
else
{
uint8_t x_396; 
lean_dec(x_1);
x_396 = lean_unbox(x_324);
if (x_396 == 0)
{
uint8_t x_397; 
x_397 = lean_unbox(x_322);
if (x_397 == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_326);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_312);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_287);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_398 = l_Lean_mkAppN(x_10, x_320);
lean_dec(x_320);
x_399 = lean_box(0);
x_400 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
x_401 = lean_unbox(x_390);
lean_dec(x_390);
lean_ctor_set_uint8(x_400, sizeof(void*)*2, x_401);
x_402 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_402, 0, x_400);
if (lean_is_scalar(x_295)) {
 x_403 = lean_alloc_ctor(0, 2, 0);
} else {
 x_403 = x_295;
}
lean_ctor_set(x_403, 0, x_402);
lean_ctor_set(x_403, 1, x_316);
return x_403;
}
else
{
lean_dec(x_390);
lean_dec(x_295);
lean_dec(x_10);
goto block_389;
}
}
else
{
lean_dec(x_390);
lean_dec(x_295);
lean_dec(x_10);
goto block_389;
}
}
block_340:
{
uint8_t x_331; 
x_331 = lean_unbox(x_324);
lean_dec(x_324);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_328);
x_332 = lean_box(0);
x_333 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_333, 0, x_329);
lean_ctor_set(x_333, 1, x_332);
lean_ctor_set_uint8(x_333, sizeof(void*)*2, x_327);
if (lean_is_scalar(x_275)) {
 x_334 = lean_alloc_ctor(1, 1, 0);
} else {
 x_334 = x_275;
}
lean_ctor_set(x_334, 0, x_333);
if (lean_is_scalar(x_317)) {
 x_335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_335 = x_317;
}
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_330);
return x_335;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
if (lean_is_scalar(x_275)) {
 x_336 = lean_alloc_ctor(1, 1, 0);
} else {
 x_336 = x_275;
}
lean_ctor_set(x_336, 0, x_328);
x_337 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_337, 0, x_329);
lean_ctor_set(x_337, 1, x_336);
lean_ctor_set_uint8(x_337, sizeof(void*)*2, x_327);
x_338 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_338, 0, x_337);
if (lean_is_scalar(x_317)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_317;
}
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_330);
return x_339;
}
}
block_389:
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_341 = lean_ctor_get(x_274, 1);
lean_inc(x_341);
x_342 = lean_ctor_get(x_274, 0);
lean_inc(x_342);
lean_dec(x_274);
x_343 = lean_array_get_size(x_320);
x_344 = l_Array_toSubarray___redArg(x_320, x_298, x_343);
x_345 = lean_box(0);
if (lean_is_scalar(x_326)) {
 x_346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_346 = x_326;
}
lean_ctor_set(x_346, 0, x_299);
lean_ctor_set(x_346, 1, x_342);
if (lean_is_scalar(x_323)) {
 x_347 = lean_alloc_ctor(0, 2, 0);
} else {
 x_347 = x_323;
}
lean_ctor_set(x_347, 0, x_341);
lean_ctor_set(x_347, 1, x_346);
if (lean_is_scalar(x_321)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_321;
}
lean_ctor_set(x_348, 0, x_298);
lean_ctor_set(x_348, 1, x_347);
if (lean_is_scalar(x_319)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_319;
}
lean_ctor_set(x_349, 0, x_300);
lean_ctor_set(x_349, 1, x_348);
if (lean_is_scalar(x_312)) {
 x_350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_350 = x_312;
}
lean_ctor_set(x_350, 0, x_344);
lean_ctor_set(x_350, 1, x_349);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_345);
lean_ctor_set(x_351, 1, x_350);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_352 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2(x_318, x_287, x_307, x_308, x_351, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_316);
lean_dec(x_287);
lean_dec(x_318);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_353, 1);
lean_inc(x_354);
x_355 = lean_ctor_get(x_354, 1);
lean_inc(x_355);
lean_dec(x_354);
x_356 = lean_ctor_get(x_355, 1);
lean_inc(x_356);
lean_dec(x_355);
x_357 = lean_ctor_get(x_356, 1);
lean_inc(x_357);
lean_dec(x_356);
x_358 = lean_ctor_get(x_357, 1);
lean_inc(x_358);
x_359 = lean_ctor_get(x_353, 0);
lean_inc(x_359);
lean_dec(x_353);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
x_360 = lean_ctor_get(x_352, 1);
lean_inc(x_360);
lean_dec(x_352);
x_361 = lean_ctor_get(x_357, 0);
lean_inc(x_361);
lean_dec(x_357);
x_362 = lean_ctor_get(x_358, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_358, 1);
lean_inc(x_363);
lean_dec(x_358);
x_364 = lean_expr_instantiate_rev(x_363, x_362);
lean_dec(x_362);
lean_dec(x_363);
x_365 = lean_mk_string_unchecked("Eq", 2, 2);
x_366 = l_Lean_Name_mkStr1(x_365);
x_367 = lean_unsigned_to_nat(3u);
x_368 = l_Lean_Expr_isAppOfArity(x_364, x_366, x_367);
lean_dec(x_366);
if (x_368 == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_364);
lean_dec(x_361);
lean_dec(x_324);
lean_dec(x_322);
lean_dec(x_317);
lean_dec(x_275);
x_369 = lean_mk_string_unchecked("Lean.Meta.Tactic.Simp.Types", 27, 27);
x_370 = lean_mk_string_unchecked("Lean.Meta.Simp.tryAutoCongrTheorem\?", 35, 35);
x_371 = lean_unsigned_to_nat(756u);
x_372 = lean_unsigned_to_nat(61u);
x_373 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_374 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_369, x_370, x_371, x_372, x_373);
lean_dec(x_373);
lean_dec(x_370);
lean_dec(x_369);
x_375 = l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__4(x_374, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_360);
return x_375;
}
else
{
lean_object* x_376; uint8_t x_377; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_376 = l_Lean_Expr_appArg_x21(x_364);
lean_dec(x_364);
x_377 = lean_unbox(x_322);
lean_dec(x_322);
if (x_377 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_327 = x_368;
x_328 = x_361;
x_329 = x_376;
x_330 = x_360;
goto block_340;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = l_Lean_Meta_Simp_removeUnnecessaryCasts(x_376, x_5, x_6, x_7, x_8, x_360);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_327 = x_368;
x_328 = x_361;
x_329 = x_379;
x_330 = x_380;
goto block_340;
}
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_324);
lean_dec(x_322);
lean_dec(x_317);
lean_dec(x_275);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_381 = lean_ctor_get(x_352, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_382 = x_352;
} else {
 lean_dec_ref(x_352);
 x_382 = lean_box(0);
}
x_383 = lean_ctor_get(x_359, 0);
lean_inc(x_383);
lean_dec(x_359);
if (lean_is_scalar(x_382)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_382;
}
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_381);
return x_384;
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_324);
lean_dec(x_322);
lean_dec(x_317);
lean_dec(x_275);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_385 = lean_ctor_get(x_352, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_352, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_387 = x_352;
} else {
 lean_dec_ref(x_352);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(1, 2, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_386);
return x_388;
}
}
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_295);
lean_dec(x_287);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_404 = lean_ctor_get(x_309, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_309, 1);
lean_inc(x_405);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_406 = x_309;
} else {
 lean_dec_ref(x_309);
 x_406 = lean_box(0);
}
if (lean_is_scalar(x_406)) {
 x_407 = lean_alloc_ctor(1, 2, 0);
} else {
 x_407 = x_406;
}
lean_ctor_set(x_407, 0, x_404);
lean_ctor_set(x_407, 1, x_405);
return x_407;
}
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_287);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_408 = lean_ctor_get(x_289, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_289, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_410 = x_289;
} else {
 lean_dec_ref(x_289);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(1, 2, 0);
} else {
 x_411 = x_410;
}
lean_ctor_set(x_411, 0, x_408);
lean_ctor_set(x_411, 1, x_409);
return x_411;
}
}
}
}
}
else
{
uint8_t x_412; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_412 = !lean_is_exclusive(x_11);
if (x_412 == 0)
{
return x_11;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_413 = lean_ctor_get(x_11, 0);
x_414 = lean_ctor_get(x_11, 1);
lean_inc(x_414);
lean_inc(x_413);
lean_dec(x_11);
x_415 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set(x_415, 1, x_414);
return x_415;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__0___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_unbox(x_5);
lean_dec(x_5);
x_19 = lean_unbox(x_6);
lean_dec(x_6);
x_20 = lean_unbox(x_8);
lean_dec(x_8);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___lam__0(x_1, x_2, x_3, x_4, x_18, x_19, x_7, x_20, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__1(x_16, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2_spec__2(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_tryAutoCongrTheorem_x3f_spec__2(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_Result_addExtraArgs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_1, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_Meta_mkCongrFun(x_4, x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_4 = x_14;
x_9 = x_15;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addExtraArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_mkAppN(x_9, x_2);
x_11 = lean_box(1);
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_8);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; lean_object* x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_array_size(x_2);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_usize_of_nat(x_18);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_Result_addExtraArgs_spec__0(x_2, x_17, x_19, x_16, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l_Lean_mkAppN(x_23, x_2);
lean_ctor_set(x_8, 0, x_22);
x_25 = lean_box(1);
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_8);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_27);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = l_Lean_mkAppN(x_30, x_2);
lean_ctor_set(x_8, 0, x_28);
x_32 = lean_box(1);
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_8);
x_34 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_29);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_free_object(x_8);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_20);
if (x_36 == 0)
{
return x_20;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_20, 0);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_20);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; size_t x_41; lean_object* x_42; size_t x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_8, 0);
lean_inc(x_40);
lean_dec(x_8);
x_41 = lean_array_size(x_2);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_usize_of_nat(x_42);
x_44 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_Result_addExtraArgs_spec__0(x_2, x_41, x_43, x_40, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = l_Lean_mkAppN(x_48, x_2);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_51 = lean_box(1);
x_52 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_unbox(x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_53);
if (lean_is_scalar(x_47)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_47;
}
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_46);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_1);
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_44, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_57 = x_44;
} else {
 lean_dec_ref(x_44);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_Result_addExtraArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_Result_addExtraArgs_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addExtraArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Result_addExtraArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_addExtraArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_Lean_Meta_Simp_Result_addExtraArgs(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_ctor_set(x_1, 0, x_12);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_1, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_free_object(x_1);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lean_Meta_Simp_Result_addExtraArgs(x_20, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_29 = x_21;
} else {
 lean_dec_ref(x_21);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(1, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
case 1:
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = l_Lean_Meta_Simp_Result_addExtraArgs(x_32, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_ctor_set(x_1, 0, x_35);
lean_ctor_set(x_33, 0, x_1);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_33);
lean_ctor_set(x_1, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_1);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_33);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
lean_dec(x_1);
x_44 = l_Lean_Meta_Simp_Result_addExtraArgs(x_43, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_45);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_52 = x_44;
} else {
 lean_dec_ref(x_44);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
default: 
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_7);
return x_55;
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_1);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_1, 0);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_54);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_54, 0);
x_60 = l_Lean_Meta_Simp_Result_addExtraArgs(x_59, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 0);
lean_ctor_set(x_54, 0, x_62);
lean_ctor_set(x_60, 0, x_1);
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_60, 0);
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_60);
lean_ctor_set(x_54, 0, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_free_object(x_54);
lean_free_object(x_1);
x_66 = !lean_is_exclusive(x_60);
if (x_66 == 0)
{
return x_60;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_60, 0);
x_68 = lean_ctor_get(x_60, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_60);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_54, 0);
lean_inc(x_70);
lean_dec(x_54);
x_71 = l_Lean_Meta_Simp_Result_addExtraArgs(x_70, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_1, 0, x_75);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_free_object(x_1);
x_77 = lean_ctor_get(x_71, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_79 = x_71;
} else {
 lean_dec_ref(x_71);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_1);
x_81 = lean_ctor_get(x_54, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_82 = x_54;
} else {
 lean_dec_ref(x_54);
 x_82 = lean_box(0);
}
x_83 = l_Lean_Meta_Simp_Result_addExtraArgs(x_81, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_87 = lean_alloc_ctor(1, 1, 0);
} else {
 x_87 = x_82;
}
lean_ctor_set(x_87, 0, x_84);
x_88 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_88, 0, x_87);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_86;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_85);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_82);
x_90 = lean_ctor_get(x_83, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_83, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_92 = x_83;
} else {
 lean_dec_ref(x_83);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_addExtraArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Step_addExtraArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DStep_addExtraArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_mkAppN(x_4, x_2);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_mkAppN(x_6, x_2);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
case 1:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = l_Lean_mkAppN(x_10, x_2);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_mkAppN(x_12, x_2);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
default: 
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
return x_1;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = l_Lean_mkAppN(x_19, x_2);
lean_ctor_set(x_15, 0, x_20);
return x_1;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
x_22 = l_Lean_mkAppN(x_21, x_2);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_25 = x_15;
} else {
 lean_dec_ref(x_15);
 x_25 = lean_box(0);
}
x_26 = l_Lean_mkAppN(x_24, x_2);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DStep_addExtraArgs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_DStep_addExtraArgs(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Meta_Simp_Result_addLambdas_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; 
x_12 = l_Array_isEmpty___redArg(x_1);
x_13 = lean_box(1);
x_14 = lean_box(1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_sub(x_3, x_16);
x_23 = lean_array_uget(x_2, x_17);
x_24 = lean_mk_empty_array_with_capacity(x_15);
x_25 = lean_array_push(x_24, x_23);
x_26 = lean_unbox(x_13);
x_27 = lean_unbox(x_14);
x_28 = l_Lean_Meta_mkLambdaFVars(x_25, x_5, x_12, x_26, x_12, x_27, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_31 = l_Lean_Meta_mkFunExt(x_29, x_6, x_7, x_8, x_9, x_30);
x_18 = x_31;
goto block_22;
}
else
{
x_18 = x_28;
goto block_22;
}
block_22:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_3 = x_17;
x_5 = x_19;
x_10 = x_20;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_18;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_10);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addLambdas(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Array_isEmpty___redArg(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_box(1);
x_11 = lean_box(1);
x_12 = lean_unbox(x_10);
x_13 = lean_unbox(x_11);
x_14 = l_Lean_Meta_mkLambdaFVars(x_2, x_9, x_8, x_12, x_8, x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_25; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_unbox(x_10);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_16);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_array_get_size(x_2);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_lt(x_31, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = x_29;
x_19 = x_16;
goto block_24;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_34 = lean_usize_of_nat(x_31);
x_35 = l_Array_foldrMUnsafe_fold___at___Lean_Meta_Simp_Result_addLambdas_spec__0(x_2, x_2, x_33, x_34, x_29, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_18 = x_36;
x_19 = x_37;
goto block_24;
}
else
{
uint8_t x_38; 
lean_dec(x_17);
lean_dec(x_15);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_35);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
block_24:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_unbox(x_10);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_22);
if (lean_is_scalar(x_17)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_17;
}
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
else
{
uint8_t x_42; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_14);
if (x_42 == 0)
{
return x_14;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_14);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_7);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Meta_Simp_Result_addLambdas_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldrMUnsafe_fold___at___Lean_Meta_Simp_Result_addLambdas_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addLambdas___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Result_addLambdas(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Meta_Simp_Result_addForalls_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; 
x_12 = l_Array_isEmpty___redArg(x_1);
x_13 = lean_box(1);
x_14 = lean_box(1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_sub(x_3, x_16);
x_23 = lean_array_uget(x_2, x_17);
x_24 = lean_mk_empty_array_with_capacity(x_15);
x_25 = lean_array_push(x_24, x_23);
x_26 = lean_unbox(x_13);
x_27 = lean_unbox(x_14);
x_28 = l_Lean_Meta_mkLambdaFVars(x_25, x_5, x_12, x_26, x_12, x_27, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_31 = l_Lean_Meta_mkForallCongr(x_29, x_6, x_7, x_8, x_9, x_30);
x_18 = x_31;
goto block_22;
}
else
{
x_18 = x_28;
goto block_22;
}
block_22:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_3 = x_17;
x_5 = x_19;
x_10 = x_20;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_18;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_10);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addForalls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Array_isEmpty___redArg(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_box(1);
x_11 = lean_box(1);
x_12 = lean_unbox(x_10);
x_13 = lean_unbox(x_11);
x_14 = l_Lean_Meta_mkForallFVars(x_2, x_9, x_8, x_12, x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_25; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_unbox(x_10);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_16);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_array_get_size(x_2);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_lt(x_31, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = x_29;
x_19 = x_16;
goto block_24;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_34 = lean_usize_of_nat(x_31);
x_35 = l_Array_foldrMUnsafe_fold___at___Lean_Meta_Simp_Result_addForalls_spec__0(x_2, x_2, x_33, x_34, x_29, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_18 = x_36;
x_19 = x_37;
goto block_24;
}
else
{
uint8_t x_38; 
lean_dec(x_17);
lean_dec(x_15);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_35);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
block_24:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_unbox(x_10);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_22);
if (lean_is_scalar(x_17)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_17;
}
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
else
{
uint8_t x_42; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_14);
if (x_42 == 0)
{
return x_14;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_14);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_7);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Meta_Simp_Result_addForalls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldrMUnsafe_fold___at___Lean_Meta_Simp_Result_addForalls_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_addForalls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Result_addForalls(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_expr_eqv(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_10, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
x_16 = l_Lean_MVarId_replaceTargetEq(x_1, x_15, x_14, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_applySimpResultToTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_applySimpResultToTarget(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CongrTheorems(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CongrTheorems(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Simp_instInhabitedResult = _init_l_Lean_Meta_Simp_instInhabitedResult();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedResult);
l_Lean_Meta_Simp_instInhabitedContext = _init_l_Lean_Meta_Simp_instInhabitedContext();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext);
l_Lean_Meta_Simp_instInhabitedUsedSimps = _init_l_Lean_Meta_Simp_instInhabitedUsedSimps();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedUsedSimps);
l_Lean_Meta_Simp_instInhabitedDiagnostics = _init_l_Lean_Meta_Simp_instInhabitedDiagnostics();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedDiagnostics);
l_Lean_Meta_Simp_instInhabitedStats = _init_l_Lean_Meta_Simp_instInhabitedStats();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedStats);
l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_MethodsRefPointed = _init_l___private_Lean_Meta_Tactic_Simp_Types_0__Lean_Meta_Simp_MethodsRefPointed();
l_Lean_Meta_Simp_instInhabitedStep = _init_l_Lean_Meta_Simp_instInhabitedStep();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedStep);
l_Lean_Meta_Simp_instAndThenSimproc = _init_l_Lean_Meta_Simp_instAndThenSimproc();
lean_mark_persistent(l_Lean_Meta_Simp_instAndThenSimproc);
l_Lean_Meta_Simp_instAndThenDSimproc = _init_l_Lean_Meta_Simp_instAndThenDSimproc();
lean_mark_persistent(l_Lean_Meta_Simp_instAndThenDSimproc);
l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry = _init_l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocOLeanEntry);
l_Lean_Meta_Simp_instInhabitedSimprocs = _init_l_Lean_Meta_Simp_instInhabitedSimprocs();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocs);
l_Lean_Meta_Simp_instInhabitedMethods = _init_l_Lean_Meta_Simp_instInhabitedMethods();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedMethods);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
