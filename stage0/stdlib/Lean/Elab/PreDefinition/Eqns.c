// Lean compiler output
// Module: Lean.Elab.PreDefinition.Eqns
// Imports: Lean.Meta.Eqns Lean.Meta.CtorRecognizer Lean.Util.CollectFVars Lean.Util.ForEachExprWhere Lean.Meta.Tactic.Split Lean.Meta.Tactic.Apply Lean.Meta.Tactic.Refl Lean.Meta.Match.MatchEqs
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
lean_object* l_Lean_Meta_Match_unfoldNamedPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assumptionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkEqns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_initFn____x40_Lean_Elab_PreDefinition_Eqns___hyg_7734_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_lhsDependsOn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_contradictionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___Lean_Elab_Eqns_mkUnfoldProof_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_splitMatch_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkEqns_doRealize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPostponed___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_reduce_visit_spec__6___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkEqns___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Meta_Match_isNamedPattern___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Eqns_mkUnfoldProof_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Eqns_mkEqns_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_List_allM___at___Lean_Elab_Eqns_mkUnfoldProof_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__10_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_expand___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_splitMatch_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpMatch_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Eqns_mkUnfoldProof_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaRHS_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_removeUnusedEqnHypotheses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_tactic_hygienic;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelMVars_visitExpr_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryContradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldThmType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_instMonadLiftT(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldLHS___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
extern lean_object* l_Lean_Meta_backward_eqns_deepRecursiveSplit;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_Lean_Meta_smartUnfolding;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___Lean_Elab_Eqns_mkUnfoldProof_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldLHS___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVar_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkForall(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldThmType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpEqnType_collect___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkUnfoldProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpEqnType_collect(lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Eqns_mkEqns_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___Lean_Elab_Eqns_mkUnfoldProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpEqnType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_delta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_commitWhenSome_x3f___at_____private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkUnfoldProof_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaRHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaRHS_x3f___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkUnfoldProof___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at___Lean_Meta_removeUnused_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_lhsDependsOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_expand(uint8_t, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Split_splitMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldThmType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpEqnType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpEqnType_collect___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isAppOf___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpIfTarget(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_removeUnusedEqnHypotheses_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_expandRHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getResetPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpIf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__10_spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkEqnTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_find_ext_expr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpEqnType_collect___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBTree_toArray___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_commitWhen___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_splitTarget_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_whnfAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_lhsDependsOn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_LocalContext_getFVars_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_Match_isNamedPattern_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_removeUnusedEqnHypotheses_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Split_simpMatchTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldThmType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_instInhabitedEqnInfoCore;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__14___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaRHS_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkUnfoldProof___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryContradiction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Meta_sortFVarIds___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_runST___redArg(lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6_spec__7_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Eqns_mkEqns_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Eqns_deltaRHS_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkEqns_doRealize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof_go_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkEqnTypes_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isBRecOnRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_pushDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_pushDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldLHS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___Lean_Elab_Eqns_mkUnfoldProof_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_ForEachExprWhere_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_splitMatch_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_casesOnStuckLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_removeUnusedEqnHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__0(lean_object*, lean_object*, size_t, size_t);
lean_object* l_panic___at___Lean_Meta_subst_substEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLambda(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpTargetStar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkEqns___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
LEAN_EXPORT uint8_t l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2_spec__2___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldThmType___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelMVars_visitExpr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___Lean_Elab_Eqns_mkUnfoldProof_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_Elab_Eqns_deltaLHS___lam__0(uint8_t, lean_object*);
lean_object* l_Lean_Expr_letFun_x3f(lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_whnfAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___Lean_Elab_Eqns_mkUnfoldProof_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_setPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkEqns(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_splitMatch_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpMatch_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Eqns_mkEqns_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_reduce_visit_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_processPostponed(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Eqns_instInhabitedEqnInfoCore() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_6);
lean_ctor_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_expand(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 8:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(1);
x_6 = lean_expr_instantiate1(x_4, x_3);
lean_dec(x_3);
lean_dec(x_4);
x_7 = lean_unbox(x_5);
x_1 = x_7;
x_2 = x_6;
goto _start;
}
case 10:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_1 = x_11;
x_2 = x_9;
goto _start;
}
default: 
{
lean_object* x_13; 
lean_inc(x_2);
x_13 = l_Lean_Expr_letFun_x3f(x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(1);
x_22 = lean_expr_instantiate1(x_20, x_19);
lean_dec(x_19);
lean_dec(x_20);
x_23 = lean_unbox(x_21);
x_1 = x_23;
x_2 = x_22;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_expand___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Elab_Eqns_expand(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_expandRHS_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_MVarId_getType_x27(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = l_Lean_Expr_appArg_x21(x_9);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Elab_Eqns_expand(x_18, x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_box(0);
lean_ctor_set(x_7, 0, x_22);
return x_7;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_7);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_Expr_appFn_x21(x_9);
lean_dec(x_9);
x_25 = l_Lean_Expr_appArg_x21(x_24);
lean_dec(x_24);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_26 = l_Lean_Meta_mkEq(x_25, x_23, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_27, x_2, x_3, x_4, x_5, x_28);
lean_dec(x_2);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_26);
if (x_41 == 0)
{
return x_26;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_26, 0);
x_43 = lean_ctor_get(x_26, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_26);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_7, 0);
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_7);
x_47 = lean_mk_string_unchecked("Eq", 2, 2);
x_48 = l_Lean_Name_mkStr1(x_47);
x_49 = lean_unsigned_to_nat(3u);
x_50 = l_Lean_Expr_isAppOfArity(x_45, x_48, x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_45);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_46);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_53 = l_Lean_Expr_appArg_x21(x_45);
x_54 = lean_box(0);
x_55 = lean_unbox(x_54);
x_56 = l_Lean_Elab_Eqns_expand(x_55, x_53);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_56);
lean_dec(x_45);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_46);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_dec(x_56);
x_62 = l_Lean_Expr_appFn_x21(x_45);
lean_dec(x_45);
x_63 = l_Lean_Expr_appArg_x21(x_62);
lean_dec(x_62);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_64 = l_Lean_Meta_mkEq(x_63, x_61, x_2, x_3, x_4, x_5, x_46);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_65, x_2, x_3, x_4, x_5, x_66);
lean_dec(x_2);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_68);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_67, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_67, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_75 = x_67;
} else {
 lean_dec_ref(x_67);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = lean_ctor_get(x_64, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_64, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_79 = x_64;
} else {
 lean_dec_ref(x_64);
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
}
}
else
{
uint8_t x_81; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_7);
if (x_81 == 0)
{
return x_7;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_7, 0);
x_83 = lean_ctor_get(x_7, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_7);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpMatch_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_Split_simpMatchTarget(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_name_eq(x_1, x_9);
lean_dec(x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_box(0);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_name_eq(x_1, x_13);
lean_dec(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpMatch_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Eqns_simpMatch_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpIf_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
lean_inc(x_1);
x_9 = l_Lean_Meta_simpIfTarget(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_name_eq(x_1, x_11);
lean_dec(x_1);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_box(0);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_name_eq(x_1, x_15);
lean_dec(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
lean_dec(x_1);
return x_8;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
return x_14;
}
}
}
LEAN_EXPORT uint8_t l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_instInhabitedExpr;
x_8 = lean_array_get(x_7, x_1, x_4);
x_9 = l_Lean_Expr_isFVar(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
goto _start;
}
else
{
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__1___redArg(x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2_spec__2___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
return x_2;
}
else
{
if (x_6 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
lean_inc(x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_Expr_isAppOf___boxed), 2, 1);
lean_closure_set(x_7, 0, x_3);
x_8 = lean_usize_of_nat(x_4);
x_9 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_10 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__0(x_7, x_1, x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasLooseBVars(x_3);
lean_dec(x_3);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_nat_dec_lt(x_7, x_13);
if (x_14 == 0)
{
lean_dec(x_7);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = lean_box(x_3);
lean_inc(x_2);
x_17 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_instInhabitedExpr;
x_21 = lean_array_get(x_20, x_1, x_7);
x_22 = lean_find_expr(x_17, x_21);
lean_dec(x_21);
lean_dec(x_17);
if (lean_obj_tag(x_22) == 0)
{
x_8 = x_19;
goto block_12;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
if (x_4 == 0)
{
lean_free_object(x_22);
x_8 = x_19;
goto block_12;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_2);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_18);
return x_26;
}
}
else
{
lean_dec(x_22);
if (x_4 == 0)
{
x_8 = x_19;
goto block_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_18);
return x_29;
}
}
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 2);
x_10 = lean_nat_add(x_7, x_9);
lean_dec(x_7);
x_6 = x_8;
x_7 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2_spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_nat_dec_lt(x_7, x_13);
if (x_14 == 0)
{
lean_dec(x_2);
lean_inc(x_6);
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_box(0);
x_16 = lean_box(x_3);
lean_inc(x_2);
x_17 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_instInhabitedExpr;
x_21 = lean_array_get(x_20, x_1, x_7);
x_22 = lean_find_expr(x_17, x_21);
lean_dec(x_21);
lean_dec(x_17);
if (lean_obj_tag(x_22) == 0)
{
x_8 = x_19;
goto block_12;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
if (x_4 == 0)
{
lean_free_object(x_22);
x_8 = x_19;
goto block_12;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
lean_dec(x_2);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_18);
return x_26;
}
}
else
{
lean_dec(x_22);
if (x_4 == 0)
{
x_8 = x_19;
goto block_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_19);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_18);
return x_29;
}
}
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 2);
x_10 = lean_nat_add(x_7, x_9);
x_11 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_12; uint8_t x_59; 
x_59 = l_Lean_Expr_hasLooseBVars(x_5);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; uint64_t x_62; lean_object* x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; lean_object* x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; size_t x_71; size_t x_72; lean_object* x_73; size_t x_74; size_t x_75; size_t x_76; lean_object* x_77; uint8_t x_78; 
x_60 = lean_ctor_get(x_4, 1);
x_61 = lean_array_get_size(x_60);
x_62 = l_Lean_Expr_hash(x_5);
x_63 = lean_unsigned_to_nat(32u);
x_64 = lean_uint64_of_nat(x_63);
x_65 = lean_uint64_shift_right(x_62, x_64);
x_66 = lean_uint64_xor(x_62, x_65);
x_67 = lean_unsigned_to_nat(16u);
x_68 = lean_uint64_of_nat(x_67);
x_69 = lean_uint64_shift_right(x_66, x_68);
x_70 = lean_uint64_xor(x_66, x_69);
x_71 = lean_uint64_to_usize(x_70);
x_72 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_usize_of_nat(x_73);
x_75 = lean_usize_sub(x_72, x_74);
x_76 = lean_usize_land(x_71, x_75);
x_77 = lean_array_uget(x_60, x_76);
x_78 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelMVars_visitExpr_spec__0___redArg(x_5, x_77);
lean_dec(x_77);
x_12 = x_78;
goto block_58;
}
else
{
x_12 = x_59;
goto block_58;
}
block_11:
{
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(2);
x_10 = lean_unbox(x_9);
return x_10;
}
}
block_58:
{
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_1);
x_13 = l_Lean_Meta_isMatcherAppCore_x3f(x_1, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = l_Lean_Expr_getAppFn(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_mk_string_unchecked("WellFounded", 11, 11);
x_17 = lean_mk_string_unchecked("fix", 3, 3);
x_18 = l_Lean_Name_mkStr2(x_16, x_17);
x_19 = lean_name_eq(x_15, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_isBRecOnRecursor(x_1, x_15);
x_6 = x_20;
goto block_11;
}
else
{
lean_dec(x_15);
lean_dec(x_1);
x_6 = x_19;
goto block_11;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_14);
lean_dec(x_1);
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_box(0);
x_25 = l_Lean_Expr_sort___override(x_24);
x_26 = l_Lean_Expr_getAppNumArgs(x_5);
lean_inc(x_26);
x_27 = lean_mk_array(x_26, x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_26, x_28);
lean_dec(x_26);
x_30 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_5, x_27, x_29);
x_31 = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(x_23);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
x_33 = lean_nat_add(x_31, x_32);
lean_dec(x_32);
lean_inc(x_31);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_28);
x_35 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__1___redArg(x_30, x_34, x_12, x_31);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
lean_dec(x_30);
lean_dec(x_23);
lean_dec(x_2);
x_36 = lean_box(1);
x_37 = lean_unbox(x_36);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = l_Array_isEmpty___redArg(x_2);
if (x_38 == 0)
{
if (x_3 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(x_23);
x_40 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_23);
lean_dec(x_23);
x_41 = lean_nat_add(x_39, x_40);
lean_dec(x_40);
lean_inc(x_39);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_28);
x_43 = lean_box(0);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2___redArg(x_30, x_2, x_12, x_35, x_42, x_45, x_39);
lean_dec(x_39);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_30);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_box(1);
x_49 = lean_unbox(x_48);
return x_49;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
return x_51;
}
}
else
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_30);
lean_dec(x_23);
lean_dec(x_2);
x_52 = lean_box(0);
x_53 = lean_unbox(x_52);
return x_53;
}
}
else
{
lean_object* x_54; uint8_t x_55; 
lean_dec(x_30);
lean_dec(x_23);
lean_dec(x_2);
x_54 = lean_box(0);
x_55 = lean_unbox(x_54);
return x_55;
}
}
}
}
else
{
lean_object* x_56; uint8_t x_57; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_box(1);
x_57 = lean_unbox(x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f___lam__0___boxed), 5, 4);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_6);
lean_closure_set(x_7, 3, x_5);
x_8 = lean_find_ext_expr(x_7, x_3);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__1___redArg(x_1, x_2, x_5, x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__1(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2_spec__2___redArg___lam__0(x_1, x_4, x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2_spec__2___redArg(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2_spec__2(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2___redArg(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f_spec__2(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f___lam__0(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_4);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_splitMatch_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_14; uint8_t x_15; 
x_14 = lean_st_ref_get(x_8, x_9);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_7, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_Meta_backward_eqns_deepRecursiveSplit;
x_21 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_18, x_20);
lean_dec(x_18);
lean_inc(x_4);
lean_inc(x_2);
x_22 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f(x_21, x_19, x_3, x_2, x_4);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_4);
lean_dec(x_2);
x_23 = lean_mk_string_unchecked("Meta", 4, 4);
x_24 = lean_mk_string_unchecked("Tactic", 6, 6);
x_25 = lean_mk_string_unchecked("split", 5, 5);
x_26 = l_Lean_Name_mkStr3(x_23, x_24, x_25);
lean_inc(x_26);
x_27 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_26, x_5, x_6, x_7, x_8, x_17);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_26);
lean_free_object(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_10 = x_30;
goto block_13;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_27, 1);
x_33 = lean_ctor_get(x_27, 0);
lean_dec(x_33);
x_34 = lean_mk_string_unchecked("did not find term to split\n", 27, 27);
x_35 = l_Lean_stringToMessageData(x_34);
lean_dec(x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_36);
lean_ctor_set(x_27, 0, x_35);
x_37 = lean_mk_string_unchecked("", 0, 0);
x_38 = l_Lean_stringToMessageData(x_37);
lean_dec(x_37);
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_38);
lean_ctor_set(x_14, 0, x_27);
x_39 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_26, x_14, x_5, x_6, x_7, x_8, x_32);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_10 = x_40;
goto block_13;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_dec(x_27);
x_42 = lean_mk_string_unchecked("did not find term to split\n", 27, 27);
x_43 = l_Lean_stringToMessageData(x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_1);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_mk_string_unchecked("", 0, 0);
x_47 = l_Lean_stringToMessageData(x_46);
lean_dec(x_46);
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_47);
lean_ctor_set(x_14, 0, x_45);
x_48 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_26, x_14, x_5, x_6, x_7, x_8, x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_10 = x_49;
goto block_13;
}
}
}
else
{
uint8_t x_50; 
lean_free_object(x_14);
x_50 = !lean_is_exclusive(x_22);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_22, 0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_51);
lean_inc(x_1);
x_52 = l_Lean_Meta_Split_splitMatch(x_1, x_51, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
lean_dec(x_51);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_ctor_set(x_22, 0, x_54);
lean_ctor_set(x_52, 0, x_22);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_52);
lean_ctor_set(x_22, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_22);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_free_object(x_22);
x_58 = !lean_is_exclusive(x_52);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_115; 
x_59 = lean_ctor_get(x_52, 0);
x_60 = lean_ctor_get(x_52, 1);
lean_inc(x_60);
lean_inc(x_59);
x_115 = l_Lean_Exception_isInterrupt(x_59);
if (x_115 == 0)
{
uint8_t x_116; 
x_116 = l_Lean_Exception_isRuntime(x_59);
lean_dec(x_59);
x_61 = x_116;
goto block_114;
}
else
{
lean_dec(x_59);
x_61 = x_115;
goto block_114;
}
block_114:
{
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; lean_object* x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; size_t x_74; size_t x_75; lean_object* x_76; size_t x_77; size_t x_78; size_t x_79; lean_object* x_80; uint8_t x_81; 
lean_dec(x_52);
x_62 = lean_ctor_get(x_4, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_4, 1);
lean_inc(x_63);
x_64 = lean_array_get_size(x_63);
x_65 = l_Lean_Expr_hash(x_51);
x_66 = lean_unsigned_to_nat(32u);
x_67 = lean_uint64_of_nat(x_66);
x_68 = lean_uint64_shift_right(x_65, x_67);
x_69 = lean_uint64_xor(x_65, x_68);
x_70 = lean_unsigned_to_nat(16u);
x_71 = lean_uint64_of_nat(x_70);
x_72 = lean_uint64_shift_right(x_69, x_71);
x_73 = lean_uint64_xor(x_69, x_72);
x_74 = lean_uint64_to_usize(x_73);
x_75 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_usize_of_nat(x_76);
x_78 = lean_usize_sub(x_75, x_77);
x_79 = lean_usize_land(x_74, x_78);
x_80 = lean_array_uget(x_63, x_79);
x_81 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelMVars_visitExpr_spec__0___redArg(x_51, x_80);
if (x_81 == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_4);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_83 = lean_ctor_get(x_4, 1);
lean_dec(x_83);
x_84 = lean_ctor_get(x_4, 0);
lean_dec(x_84);
x_85 = lean_box(0);
x_86 = lean_nat_add(x_62, x_76);
lean_dec(x_62);
x_87 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_87, 0, x_51);
lean_ctor_set(x_87, 1, x_85);
lean_ctor_set(x_87, 2, x_80);
x_88 = lean_array_uset(x_63, x_79, x_87);
x_89 = lean_unsigned_to_nat(2u);
x_90 = lean_nat_shiftl(x_86, x_89);
x_91 = lean_unsigned_to_nat(3u);
x_92 = lean_nat_div(x_90, x_91);
lean_dec(x_90);
x_93 = lean_array_get_size(x_88);
x_94 = lean_nat_dec_le(x_92, x_93);
lean_dec(x_93);
lean_dec(x_92);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelMVars_visitExpr_spec__1___redArg(x_88);
lean_ctor_set(x_4, 1, x_95);
lean_ctor_set(x_4, 0, x_86);
x_9 = x_60;
goto _start;
}
else
{
lean_ctor_set(x_4, 1, x_88);
lean_ctor_set(x_4, 0, x_86);
x_9 = x_60;
goto _start;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_4);
x_98 = lean_box(0);
x_99 = lean_nat_add(x_62, x_76);
lean_dec(x_62);
x_100 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_100, 0, x_51);
lean_ctor_set(x_100, 1, x_98);
lean_ctor_set(x_100, 2, x_80);
x_101 = lean_array_uset(x_63, x_79, x_100);
x_102 = lean_unsigned_to_nat(2u);
x_103 = lean_nat_shiftl(x_99, x_102);
x_104 = lean_unsigned_to_nat(3u);
x_105 = lean_nat_div(x_103, x_104);
lean_dec(x_103);
x_106 = lean_array_get_size(x_101);
x_107 = lean_nat_dec_le(x_105, x_106);
lean_dec(x_106);
lean_dec(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelMVars_visitExpr_spec__1___redArg(x_101);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_99);
lean_ctor_set(x_109, 1, x_108);
x_4 = x_109;
x_9 = x_60;
goto _start;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_99);
lean_ctor_set(x_111, 1, x_101);
x_4 = x_111;
x_9 = x_60;
goto _start;
}
}
}
else
{
lean_dec(x_80);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_51);
x_9 = x_60;
goto _start;
}
}
else
{
lean_dec(x_60);
lean_dec(x_51);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_52;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_159; 
x_117 = lean_ctor_get(x_52, 0);
x_118 = lean_ctor_get(x_52, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_52);
lean_inc(x_118);
lean_inc(x_117);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_159 = l_Lean_Exception_isInterrupt(x_117);
if (x_159 == 0)
{
uint8_t x_160; 
x_160 = l_Lean_Exception_isRuntime(x_117);
lean_dec(x_117);
x_120 = x_160;
goto block_158;
}
else
{
lean_dec(x_117);
x_120 = x_159;
goto block_158;
}
block_158:
{
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint64_t x_124; lean_object* x_125; uint64_t x_126; uint64_t x_127; uint64_t x_128; lean_object* x_129; uint64_t x_130; uint64_t x_131; uint64_t x_132; size_t x_133; size_t x_134; lean_object* x_135; size_t x_136; size_t x_137; size_t x_138; lean_object* x_139; uint8_t x_140; 
lean_dec(x_119);
x_121 = lean_ctor_get(x_4, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_4, 1);
lean_inc(x_122);
x_123 = lean_array_get_size(x_122);
x_124 = l_Lean_Expr_hash(x_51);
x_125 = lean_unsigned_to_nat(32u);
x_126 = lean_uint64_of_nat(x_125);
x_127 = lean_uint64_shift_right(x_124, x_126);
x_128 = lean_uint64_xor(x_124, x_127);
x_129 = lean_unsigned_to_nat(16u);
x_130 = lean_uint64_of_nat(x_129);
x_131 = lean_uint64_shift_right(x_128, x_130);
x_132 = lean_uint64_xor(x_128, x_131);
x_133 = lean_uint64_to_usize(x_132);
x_134 = lean_usize_of_nat(x_123);
lean_dec(x_123);
x_135 = lean_unsigned_to_nat(1u);
x_136 = lean_usize_of_nat(x_135);
x_137 = lean_usize_sub(x_134, x_136);
x_138 = lean_usize_land(x_133, x_137);
x_139 = lean_array_uget(x_122, x_138);
x_140 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelMVars_visitExpr_spec__0___redArg(x_51, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_141 = x_4;
} else {
 lean_dec_ref(x_4);
 x_141 = lean_box(0);
}
x_142 = lean_box(0);
x_143 = lean_nat_add(x_121, x_135);
lean_dec(x_121);
x_144 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_144, 0, x_51);
lean_ctor_set(x_144, 1, x_142);
lean_ctor_set(x_144, 2, x_139);
x_145 = lean_array_uset(x_122, x_138, x_144);
x_146 = lean_unsigned_to_nat(2u);
x_147 = lean_nat_shiftl(x_143, x_146);
x_148 = lean_unsigned_to_nat(3u);
x_149 = lean_nat_div(x_147, x_148);
lean_dec(x_147);
x_150 = lean_array_get_size(x_145);
x_151 = lean_nat_dec_le(x_149, x_150);
lean_dec(x_150);
lean_dec(x_149);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelMVars_visitExpr_spec__1___redArg(x_145);
if (lean_is_scalar(x_141)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_141;
}
lean_ctor_set(x_153, 0, x_143);
lean_ctor_set(x_153, 1, x_152);
x_4 = x_153;
x_9 = x_118;
goto _start;
}
else
{
lean_object* x_155; 
if (lean_is_scalar(x_141)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_141;
}
lean_ctor_set(x_155, 0, x_143);
lean_ctor_set(x_155, 1, x_145);
x_4 = x_155;
x_9 = x_118;
goto _start;
}
}
else
{
lean_dec(x_139);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_51);
x_9 = x_118;
goto _start;
}
}
else
{
lean_dec(x_118);
lean_dec(x_51);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_119;
}
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_22, 0);
lean_inc(x_161);
lean_dec(x_22);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_161);
lean_inc(x_1);
x_162 = l_Lean_Meta_Split_splitMatch(x_1, x_161, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_161);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_165 = x_162;
} else {
 lean_dec_ref(x_162);
 x_165 = lean_box(0);
}
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_163);
if (lean_is_scalar(x_165)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_165;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_164);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; uint8_t x_211; 
x_168 = lean_ctor_get(x_162, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_162, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_170 = x_162;
} else {
 lean_dec_ref(x_162);
 x_170 = lean_box(0);
}
lean_inc(x_169);
lean_inc(x_168);
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
x_211 = l_Lean_Exception_isInterrupt(x_168);
if (x_211 == 0)
{
uint8_t x_212; 
x_212 = l_Lean_Exception_isRuntime(x_168);
lean_dec(x_168);
x_172 = x_212;
goto block_210;
}
else
{
lean_dec(x_168);
x_172 = x_211;
goto block_210;
}
block_210:
{
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; uint64_t x_176; lean_object* x_177; uint64_t x_178; uint64_t x_179; uint64_t x_180; lean_object* x_181; uint64_t x_182; uint64_t x_183; uint64_t x_184; size_t x_185; size_t x_186; lean_object* x_187; size_t x_188; size_t x_189; size_t x_190; lean_object* x_191; uint8_t x_192; 
lean_dec(x_171);
x_173 = lean_ctor_get(x_4, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_4, 1);
lean_inc(x_174);
x_175 = lean_array_get_size(x_174);
x_176 = l_Lean_Expr_hash(x_161);
x_177 = lean_unsigned_to_nat(32u);
x_178 = lean_uint64_of_nat(x_177);
x_179 = lean_uint64_shift_right(x_176, x_178);
x_180 = lean_uint64_xor(x_176, x_179);
x_181 = lean_unsigned_to_nat(16u);
x_182 = lean_uint64_of_nat(x_181);
x_183 = lean_uint64_shift_right(x_180, x_182);
x_184 = lean_uint64_xor(x_180, x_183);
x_185 = lean_uint64_to_usize(x_184);
x_186 = lean_usize_of_nat(x_175);
lean_dec(x_175);
x_187 = lean_unsigned_to_nat(1u);
x_188 = lean_usize_of_nat(x_187);
x_189 = lean_usize_sub(x_186, x_188);
x_190 = lean_usize_land(x_185, x_189);
x_191 = lean_array_uget(x_174, x_190);
x_192 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelMVars_visitExpr_spec__0___redArg(x_161, x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_193 = x_4;
} else {
 lean_dec_ref(x_4);
 x_193 = lean_box(0);
}
x_194 = lean_box(0);
x_195 = lean_nat_add(x_173, x_187);
lean_dec(x_173);
x_196 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_196, 0, x_161);
lean_ctor_set(x_196, 1, x_194);
lean_ctor_set(x_196, 2, x_191);
x_197 = lean_array_uset(x_174, x_190, x_196);
x_198 = lean_unsigned_to_nat(2u);
x_199 = lean_nat_shiftl(x_195, x_198);
x_200 = lean_unsigned_to_nat(3u);
x_201 = lean_nat_div(x_199, x_200);
lean_dec(x_199);
x_202 = lean_array_get_size(x_197);
x_203 = lean_nat_dec_le(x_201, x_202);
lean_dec(x_202);
lean_dec(x_201);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
x_204 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelMVars_visitExpr_spec__1___redArg(x_197);
if (lean_is_scalar(x_193)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_193;
}
lean_ctor_set(x_205, 0, x_195);
lean_ctor_set(x_205, 1, x_204);
x_4 = x_205;
x_9 = x_169;
goto _start;
}
else
{
lean_object* x_207; 
if (lean_is_scalar(x_193)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_193;
}
lean_ctor_set(x_207, 0, x_195);
lean_ctor_set(x_207, 1, x_197);
x_4 = x_207;
x_9 = x_169;
goto _start;
}
}
else
{
lean_dec(x_191);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_161);
x_9 = x_169;
goto _start;
}
}
else
{
lean_dec(x_169);
lean_dec(x_161);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_171;
}
}
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; 
x_213 = lean_ctor_get(x_14, 0);
x_214 = lean_ctor_get(x_14, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_14);
x_215 = lean_ctor_get(x_7, 2);
lean_inc(x_215);
x_216 = lean_ctor_get(x_213, 0);
lean_inc(x_216);
lean_dec(x_213);
x_217 = l_Lean_Meta_backward_eqns_deepRecursiveSplit;
x_218 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_215, x_217);
lean_dec(x_215);
lean_inc(x_4);
lean_inc(x_2);
x_219 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_findMatchToSplit_x3f(x_218, x_216, x_3, x_2, x_4);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
lean_dec(x_4);
lean_dec(x_2);
x_220 = lean_mk_string_unchecked("Meta", 4, 4);
x_221 = lean_mk_string_unchecked("Tactic", 6, 6);
x_222 = lean_mk_string_unchecked("split", 5, 5);
x_223 = l_Lean_Name_mkStr3(x_220, x_221, x_222);
lean_inc(x_223);
x_224 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_223, x_5, x_6, x_7, x_8, x_214);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_unbox(x_225);
lean_dec(x_225);
if (x_226 == 0)
{
lean_object* x_227; 
lean_dec(x_223);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_227 = lean_ctor_get(x_224, 1);
lean_inc(x_227);
lean_dec(x_224);
x_10 = x_227;
goto block_13;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_228 = lean_ctor_get(x_224, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_229 = x_224;
} else {
 lean_dec_ref(x_224);
 x_229 = lean_box(0);
}
x_230 = lean_mk_string_unchecked("did not find term to split\n", 27, 27);
x_231 = l_Lean_stringToMessageData(x_230);
lean_dec(x_230);
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_1);
if (lean_is_scalar(x_229)) {
 x_233 = lean_alloc_ctor(7, 2, 0);
} else {
 x_233 = x_229;
 lean_ctor_set_tag(x_233, 7);
}
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
x_234 = lean_mk_string_unchecked("", 0, 0);
x_235 = l_Lean_stringToMessageData(x_234);
lean_dec(x_234);
x_236 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_235);
x_237 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_223, x_236, x_5, x_6, x_7, x_8, x_228);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
lean_dec(x_237);
x_10 = x_238;
goto block_13;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_219, 0);
lean_inc(x_239);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 x_240 = x_219;
} else {
 lean_dec_ref(x_219);
 x_240 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_239);
lean_inc(x_1);
x_241 = l_Lean_Meta_Split_splitMatch(x_1, x_239, x_5, x_6, x_7, x_8, x_214);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_239);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_244 = x_241;
} else {
 lean_dec_ref(x_241);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_245 = lean_alloc_ctor(1, 1, 0);
} else {
 x_245 = x_240;
}
lean_ctor_set(x_245, 0, x_242);
if (lean_is_scalar(x_244)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_244;
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_243);
return x_246;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_290; 
lean_dec(x_240);
x_247 = lean_ctor_get(x_241, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_241, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_249 = x_241;
} else {
 lean_dec_ref(x_241);
 x_249 = lean_box(0);
}
lean_inc(x_248);
lean_inc(x_247);
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_248);
x_290 = l_Lean_Exception_isInterrupt(x_247);
if (x_290 == 0)
{
uint8_t x_291; 
x_291 = l_Lean_Exception_isRuntime(x_247);
lean_dec(x_247);
x_251 = x_291;
goto block_289;
}
else
{
lean_dec(x_247);
x_251 = x_290;
goto block_289;
}
block_289:
{
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; uint64_t x_255; lean_object* x_256; uint64_t x_257; uint64_t x_258; uint64_t x_259; lean_object* x_260; uint64_t x_261; uint64_t x_262; uint64_t x_263; size_t x_264; size_t x_265; lean_object* x_266; size_t x_267; size_t x_268; size_t x_269; lean_object* x_270; uint8_t x_271; 
lean_dec(x_250);
x_252 = lean_ctor_get(x_4, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_4, 1);
lean_inc(x_253);
x_254 = lean_array_get_size(x_253);
x_255 = l_Lean_Expr_hash(x_239);
x_256 = lean_unsigned_to_nat(32u);
x_257 = lean_uint64_of_nat(x_256);
x_258 = lean_uint64_shift_right(x_255, x_257);
x_259 = lean_uint64_xor(x_255, x_258);
x_260 = lean_unsigned_to_nat(16u);
x_261 = lean_uint64_of_nat(x_260);
x_262 = lean_uint64_shift_right(x_259, x_261);
x_263 = lean_uint64_xor(x_259, x_262);
x_264 = lean_uint64_to_usize(x_263);
x_265 = lean_usize_of_nat(x_254);
lean_dec(x_254);
x_266 = lean_unsigned_to_nat(1u);
x_267 = lean_usize_of_nat(x_266);
x_268 = lean_usize_sub(x_265, x_267);
x_269 = lean_usize_land(x_264, x_268);
x_270 = lean_array_uget(x_253, x_269);
x_271 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelMVars_visitExpr_spec__0___redArg(x_239, x_270);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_272 = x_4;
} else {
 lean_dec_ref(x_4);
 x_272 = lean_box(0);
}
x_273 = lean_box(0);
x_274 = lean_nat_add(x_252, x_266);
lean_dec(x_252);
x_275 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_275, 0, x_239);
lean_ctor_set(x_275, 1, x_273);
lean_ctor_set(x_275, 2, x_270);
x_276 = lean_array_uset(x_253, x_269, x_275);
x_277 = lean_unsigned_to_nat(2u);
x_278 = lean_nat_shiftl(x_274, x_277);
x_279 = lean_unsigned_to_nat(3u);
x_280 = lean_nat_div(x_278, x_279);
lean_dec(x_278);
x_281 = lean_array_get_size(x_276);
x_282 = lean_nat_dec_le(x_280, x_281);
lean_dec(x_281);
lean_dec(x_280);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; 
x_283 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelMVars_visitExpr_spec__1___redArg(x_276);
if (lean_is_scalar(x_272)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_272;
}
lean_ctor_set(x_284, 0, x_274);
lean_ctor_set(x_284, 1, x_283);
x_4 = x_284;
x_9 = x_248;
goto _start;
}
else
{
lean_object* x_286; 
if (lean_is_scalar(x_272)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_272;
}
lean_ctor_set(x_286, 0, x_274);
lean_ctor_set(x_286, 1, x_276);
x_4 = x_286;
x_9 = x_248;
goto _start;
}
}
else
{
lean_dec(x_270);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_239);
x_9 = x_248;
goto _start;
}
}
else
{
lean_dec(x_248);
lean_dec(x_239);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_250;
}
}
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_splitMatch_x3f_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Eqns_splitMatch_x3f_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_splitMatch_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_MVarId_getType_x27(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(8u);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_shiftl(x_11, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_17 = l_Nat_nextPowerOfTwo(x_16);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = lean_mk_array(x_17, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_Eqns_splitMatch_x3f_go(x_1, x_2, x_9, x_20, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_3);
lean_dec(x_9);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_8);
if (x_22 == 0)
{
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_splitMatch_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_splitMatch_x3f___lam__0), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_commitWhenSome_x3f___at_____private_Lean_Meta_Match_Match_0__Lean_Meta_Match_processConstructor_spec__7___redArg(x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_lhsDependsOn___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_5);
lean_inc(x_3);
x_9 = l_Lean_Meta_matchEq_x3f(x_3, x_4, x_5, x_6, x_7, x_8);
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
x_12 = l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg(x_3, x_1, x_5, x_11);
lean_dec(x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg(x_16, x_1, x_5, x_15);
lean_dec(x_5);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_lhsDependsOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_lhsDependsOn___lam__0___boxed), 8, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0(lean_box(0), x_1, x_8, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_lhsDependsOn___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_lhsDependsOn___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_93; uint8_t x_94; 
x_13 = lean_st_ref_get(x_5, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_4, 2);
lean_inc(x_16);
x_17 = l_Lean_Meta_smartUnfolding;
x_18 = lean_box(0);
x_19 = l_Lean_diagnostics;
x_20 = lean_unbox(x_18);
x_21 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_16, x_17, x_20);
x_22 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_21, x_19);
x_93 = lean_ctor_get(x_14, 0);
lean_inc(x_93);
lean_dec(x_14);
x_94 = l_Lean_Kernel_isDiagnosticsEnabled(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
if (x_22 == 0)
{
x_23 = x_4;
x_24 = x_5;
x_25 = x_15;
goto block_58;
}
else
{
goto block_92;
}
}
else
{
if (x_22 == 0)
{
goto block_92;
}
else
{
x_23 = x_4;
x_24 = x_5;
x_25 = x_15;
goto block_58;
}
}
block_12:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_dec(x_8);
return x_7;
}
}
block_58:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 3);
lean_inc(x_28);
x_29 = l_Lean_maxRecDepth;
x_30 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_21, x_29);
x_31 = lean_ctor_get(x_23, 5);
lean_inc(x_31);
x_32 = lean_ctor_get(x_23, 6);
lean_inc(x_32);
x_33 = lean_ctor_get(x_23, 7);
lean_inc(x_33);
x_34 = lean_ctor_get(x_23, 8);
lean_inc(x_34);
x_35 = lean_ctor_get(x_23, 9);
lean_inc(x_35);
x_36 = lean_ctor_get(x_23, 10);
lean_inc(x_36);
x_37 = lean_ctor_get(x_23, 11);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_23, sizeof(void*)*13 + 1);
x_39 = lean_ctor_get(x_23, 12);
lean_inc(x_39);
lean_dec(x_23);
x_40 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_27);
lean_ctor_set(x_40, 2, x_21);
lean_ctor_set(x_40, 3, x_28);
lean_ctor_set(x_40, 4, x_30);
lean_ctor_set(x_40, 5, x_31);
lean_ctor_set(x_40, 6, x_32);
lean_ctor_set(x_40, 7, x_33);
lean_ctor_set(x_40, 8, x_34);
lean_ctor_set(x_40, 9, x_35);
lean_ctor_set(x_40, 10, x_36);
lean_ctor_set(x_40, 11, x_37);
lean_ctor_set(x_40, 12, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*13, x_22);
lean_ctor_set_uint8(x_40, sizeof(void*)*13 + 1, x_38);
x_41 = l_Lean_MVarId_refl(x_1, x_2, x_3, x_40, x_24, x_25);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_box(1);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_box(1);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_41);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_41, 0);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_inc(x_49);
x_51 = l_Lean_Exception_isInterrupt(x_49);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = l_Lean_Exception_isRuntime(x_49);
lean_dec(x_49);
x_7 = x_41;
x_8 = x_50;
x_9 = x_52;
goto block_12;
}
else
{
lean_dec(x_49);
x_7 = x_41;
x_8 = x_50;
x_9 = x_51;
goto block_12;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_41, 0);
x_54 = lean_ctor_get(x_41, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_41);
lean_inc(x_54);
lean_inc(x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Exception_isInterrupt(x_53);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = l_Lean_Exception_isRuntime(x_53);
lean_dec(x_53);
x_7 = x_55;
x_8 = x_54;
x_9 = x_57;
goto block_12;
}
else
{
lean_dec(x_53);
x_7 = x_55;
x_8 = x_54;
x_9 = x_56;
goto block_12;
}
}
}
}
block_92:
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_st_ref_take(x_5, x_15);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = l_Lean_Kernel_enableDiag(x_63, x_22);
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_61, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 3);
lean_inc(x_67);
x_68 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
lean_inc(x_69);
lean_ctor_set(x_59, 1, x_69);
lean_ctor_set(x_59, 0, x_69);
x_70 = lean_ctor_get(x_61, 5);
lean_inc(x_70);
x_71 = lean_ctor_get(x_61, 6);
lean_inc(x_71);
x_72 = lean_ctor_get(x_61, 7);
lean_inc(x_72);
lean_dec(x_61);
x_73 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_65);
lean_ctor_set(x_73, 2, x_66);
lean_ctor_set(x_73, 3, x_67);
lean_ctor_set(x_73, 4, x_59);
lean_ctor_set(x_73, 5, x_70);
lean_ctor_set(x_73, 6, x_71);
lean_ctor_set(x_73, 7, x_72);
x_74 = lean_st_ref_set(x_5, x_73, x_62);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_23 = x_4;
x_24 = x_5;
x_25 = x_75;
goto block_58;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_76 = lean_ctor_get(x_59, 0);
x_77 = lean_ctor_get(x_59, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_59);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
x_79 = l_Lean_Kernel_enableDiag(x_78, x_22);
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_76, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 3);
lean_inc(x_82);
x_83 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
lean_inc(x_84);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_ctor_get(x_76, 5);
lean_inc(x_86);
x_87 = lean_ctor_get(x_76, 6);
lean_inc(x_87);
x_88 = lean_ctor_get(x_76, 7);
lean_inc(x_88);
lean_dec(x_76);
x_89 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_89, 0, x_79);
lean_ctor_set(x_89, 1, x_80);
lean_ctor_set(x_89, 2, x_81);
lean_ctor_set(x_89, 3, x_82);
lean_ctor_set(x_89, 4, x_85);
lean_ctor_set(x_89, 5, x_86);
lean_ctor_set(x_89, 6, x_87);
lean_ctor_set(x_89, 7, x_88);
x_90 = lean_st_ref_set(x_5, x_89, x_77);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_23 = x_4;
x_24 = x_5;
x_25 = x_91;
goto block_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Eqns_tryURefl(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpEqnType_collect___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Match_isNamedPattern_x3f(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_mk_string_unchecked("Lean.Elab.PreDefinition.Eqns", 28, 28);
x_7 = lean_mk_string_unchecked("Lean.Elab.Eqns.simpEqnType.collect", 34, 34);
x_8 = lean_unsigned_to_nat(152u);
x_9 = lean_unsigned_to_nat(48u);
x_10 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_11 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_12 = l_panic___redArg(x_1, x_11);
x_13 = lean_apply_1(x_12, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_16 = l_Lean_Expr_consumeMData(x_15);
lean_dec(x_15);
x_17 = l_Lean_Expr_isFVar(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_st_ref_take(x_2, x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_fvarId_x21(x_16);
lean_dec(x_16);
x_24 = l_Lean_FVarIdSet_insert(x_21, x_23);
x_25 = lean_st_ref_set(x_2, x_24, x_22);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpEqnType_collect___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_5 = l_instMonadEST(lean_box(0), lean_box(0));
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_st_mk_ref(x_6, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_instMonadLiftT(lean_box(0));
lean_inc(x_5);
x_12 = l_instInhabitedOfMonad___redArg(x_5, x_1);
lean_inc(x_9);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_simpEqnType_collect___lam__0___boxed), 4, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_9);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Match_isNamedPattern___boxed), 1, 0);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_ForEachExprWhere_visit(lean_box(0), lean_box(0), x_7, x_11, x_5, x_14, x_13, x_2, x_16);
x_18 = lean_apply_1(x_17, x_10);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_9, x_19);
lean_dec(x_9);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpEqnType_collect(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_simpEqnType_collect___lam__1), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = l_runST___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpEqnType_collect___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Eqns_simpEqnType_collect___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_mk_string_unchecked("unexpected hypothesis in alternative", 36, 36);
x_11 = l_Lean_stringToMessageData(x_10);
lean_dec(x_10);
x_12 = l_Lean_indentExpr(x_1);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("", 0, 0);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_16, x_5, x_6, x_7, x_8, x_9);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_19; uint8_t x_25; 
x_25 = lean_usize_dec_lt(x_5, x_4);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_11);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_796; 
x_27 = lean_mk_string_unchecked("Elab", 4, 4);
x_28 = lean_mk_string_unchecked("definition", 10, 10);
x_29 = l_Lean_Name_mkStr2(x_27, x_28);
lean_inc(x_29);
x_30 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_29, x_7, x_8, x_9, x_10, x_11);
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
x_34 = lean_array_uget(x_3, x_5);
x_796 = lean_unbox(x_31);
lean_dec(x_31);
if (x_796 == 0)
{
lean_object* x_797; lean_object* x_798; 
lean_dec(x_29);
x_797 = lean_ctor_get(x_6, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_6, 1);
lean_inc(x_798);
lean_dec(x_6);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_57 = x_797;
x_58 = x_798;
x_59 = x_7;
x_60 = x_8;
x_61 = x_9;
x_62 = x_10;
x_63 = x_32;
goto block_795;
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; 
x_799 = lean_ctor_get(x_6, 0);
lean_inc(x_799);
x_800 = lean_ctor_get(x_6, 1);
lean_inc(x_800);
lean_dec(x_6);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_34);
x_801 = lean_infer_type(x_34, x_7, x_8, x_9, x_10, x_32);
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; 
x_802 = lean_ctor_get(x_801, 0);
lean_inc(x_802);
x_803 = lean_ctor_get(x_801, 1);
lean_inc(x_803);
lean_dec(x_801);
x_804 = lean_mk_string_unchecked(">> simpEqnType: ", 16, 16);
x_805 = l_Lean_stringToMessageData(x_804);
lean_dec(x_804);
x_806 = l_Lean_MessageData_ofExpr(x_802);
x_807 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_807, 0, x_805);
lean_ctor_set(x_807, 1, x_806);
x_808 = lean_mk_string_unchecked(", ", 2, 2);
x_809 = l_Lean_stringToMessageData(x_808);
lean_dec(x_808);
x_810 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_810, 0, x_807);
lean_ctor_set(x_810, 1, x_809);
lean_inc(x_800);
x_811 = l_Lean_MessageData_ofExpr(x_800);
x_812 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_812, 0, x_810);
lean_ctor_set(x_812, 1, x_811);
x_813 = lean_mk_string_unchecked("", 0, 0);
x_814 = l_Lean_stringToMessageData(x_813);
lean_dec(x_813);
x_815 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_815, 0, x_812);
lean_ctor_set(x_815, 1, x_814);
x_816 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_29, x_815, x_7, x_8, x_9, x_10, x_803);
x_817 = lean_ctor_get(x_816, 1);
lean_inc(x_817);
lean_dec(x_816);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_57 = x_799;
x_58 = x_800;
x_59 = x_7;
x_60 = x_8;
x_61 = x_9;
x_62 = x_10;
x_63 = x_817;
goto block_795;
}
else
{
uint8_t x_818; 
lean_dec(x_800);
lean_dec(x_799);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_818 = !lean_is_exclusive(x_801);
if (x_818 == 0)
{
return x_801;
}
else
{
lean_object* x_819; lean_object* x_820; lean_object* x_821; 
x_819 = lean_ctor_get(x_801, 0);
x_820 = lean_ctor_get(x_801, 1);
lean_inc(x_820);
lean_inc(x_819);
lean_dec(x_801);
x_821 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_821, 0, x_819);
lean_ctor_set(x_821, 1, x_820);
return x_821;
}
}
}
block_56:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_mk_empty_array_with_capacity(x_43);
x_45 = lean_array_push(x_44, x_34);
x_46 = lean_box(1);
x_47 = lean_unbox(x_46);
x_48 = l_Lean_Meta_mkForallFVars(x_45, x_37, x_35, x_25, x_47, x_38, x_39, x_40, x_41, x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_45);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
if (lean_is_scalar(x_33)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_33;
}
lean_ctor_set(x_51, 0, x_36);
lean_ctor_set(x_51, 1, x_49);
x_12 = x_51;
x_13 = x_50;
goto block_18;
}
else
{
uint8_t x_52; 
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
return x_48;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_48, 0);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_48);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
block_795:
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Lean_Expr_fvarId_x21(x_34);
x_65 = l_Lean_RBNode_findCore___at___Lean_Meta_removeUnused_spec__0___redArg(x_2, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_box(0);
x_67 = l_Lean_RBNode_findCore___at___Lean_Meta_removeUnused_spec__0___redArg(x_57, x_64);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_34);
x_68 = lean_infer_type(x_34, x_59, x_60, x_61, x_62, x_63);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
x_71 = l_Lean_Meta_matchEq_x3f(x_69, x_59, x_60, x_61, x_62, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; uint8_t x_74; 
lean_dec(x_64);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_unbox(x_66);
x_35 = x_74;
x_36 = x_57;
x_37 = x_58;
x_38 = x_59;
x_39 = x_60;
x_40 = x_61;
x_41 = x_62;
x_42 = x_73;
goto block_56;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
lean_dec(x_71);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_78);
x_80 = l_Lean_Meta_isExprDefEq(x_78, x_79, x_59, x_60, x_61, x_62, x_77);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
lean_dec(x_78);
lean_dec(x_64);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_unbox(x_66);
x_35 = x_84;
x_36 = x_57;
x_37 = x_58;
x_38 = x_59;
x_39 = x_60;
x_40 = x_61;
x_41 = x_62;
x_42 = x_83;
goto block_56;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
lean_dec(x_80);
lean_inc(x_64);
lean_inc(x_58);
x_86 = l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg(x_58, x_64, x_60, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
uint8_t x_89; 
lean_dec(x_78);
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_34);
lean_dec(x_33);
x_89 = !lean_is_exclusive(x_86);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_86, 1);
x_91 = lean_ctor_get(x_86, 0);
lean_dec(x_91);
lean_ctor_set(x_86, 1, x_58);
lean_ctor_set(x_86, 0, x_57);
x_12 = x_86;
x_13 = x_90;
goto block_18;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_86, 1);
lean_inc(x_92);
lean_dec(x_86);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_57);
lean_ctor_set(x_93, 1, x_58);
x_12 = x_93;
x_13 = x_92;
goto block_18;
}
}
else
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_86);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_86, 1);
x_96 = lean_ctor_get(x_86, 0);
lean_dec(x_96);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
x_97 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_lhsDependsOn(x_58, x_64, x_59, x_60, x_61, x_62, x_95);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_33);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = l_Lean_Meta_mkEqRefl(x_78, x_59, x_60, x_61, x_62, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Lean_Expr_replaceFVar(x_58, x_34, x_102);
lean_dec(x_102);
lean_dec(x_58);
lean_ctor_set(x_86, 1, x_104);
lean_ctor_set(x_86, 0, x_57);
x_12 = x_86;
x_13 = x_103;
goto block_18;
}
else
{
uint8_t x_105; 
lean_free_object(x_86);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_101);
if (x_105 == 0)
{
return x_101;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_101, 0);
x_107 = lean_ctor_get(x_101, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_101);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; uint8_t x_110; 
lean_free_object(x_86);
lean_dec(x_78);
x_109 = lean_ctor_get(x_97, 1);
lean_inc(x_109);
lean_dec(x_97);
x_110 = lean_unbox(x_66);
x_35 = x_110;
x_36 = x_57;
x_37 = x_58;
x_38 = x_59;
x_39 = x_60;
x_40 = x_61;
x_41 = x_62;
x_42 = x_109;
goto block_56;
}
}
else
{
uint8_t x_111; 
lean_free_object(x_86);
lean_dec(x_78);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_97);
if (x_111 == 0)
{
return x_97;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_97, 0);
x_113 = lean_ctor_get(x_97, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_97);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_86, 1);
lean_inc(x_115);
lean_dec(x_86);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
x_116 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_lhsDependsOn(x_58, x_64, x_59, x_60, x_61, x_62, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_unbox(x_117);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_33);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
lean_dec(x_116);
x_120 = l_Lean_Meta_mkEqRefl(x_78, x_59, x_60, x_61, x_62, x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = l_Lean_Expr_replaceFVar(x_58, x_34, x_121);
lean_dec(x_121);
lean_dec(x_58);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_57);
lean_ctor_set(x_124, 1, x_123);
x_12 = x_124;
x_13 = x_122;
goto block_18;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_125 = lean_ctor_get(x_120, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_120, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_127 = x_120;
} else {
 lean_dec_ref(x_120);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
else
{
lean_object* x_129; uint8_t x_130; 
lean_dec(x_78);
x_129 = lean_ctor_get(x_116, 1);
lean_inc(x_129);
lean_dec(x_116);
x_130 = lean_unbox(x_66);
x_35 = x_130;
x_36 = x_57;
x_37 = x_58;
x_38 = x_59;
x_39 = x_60;
x_40 = x_61;
x_41 = x_62;
x_42 = x_129;
goto block_56;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_78);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_131 = lean_ctor_get(x_116, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_116, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_133 = x_116;
} else {
 lean_dec_ref(x_116);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_78);
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_80);
if (x_135 == 0)
{
return x_80;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_80, 0);
x_137 = lean_ctor_get(x_80, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_80);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_71);
if (x_139 == 0)
{
return x_71;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_71, 0);
x_141 = lean_ctor_get(x_71, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_71);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_68);
if (x_143 == 0)
{
return x_68;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_68, 0);
x_145 = lean_ctor_get(x_68, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_68);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
lean_dec(x_67);
lean_dec(x_33);
lean_inc(x_58);
x_147 = l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg(x_58, x_64, x_60, x_63);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_unbox(x_148);
lean_dec(x_148);
if (x_149 == 0)
{
uint8_t x_150; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_34);
x_150 = !lean_is_exclusive(x_147);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_147, 1);
x_152 = lean_ctor_get(x_147, 0);
lean_dec(x_152);
lean_ctor_set(x_147, 1, x_58);
lean_ctor_set(x_147, 0, x_57);
x_12 = x_147;
x_13 = x_151;
goto block_18;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_147, 1);
lean_inc(x_153);
lean_dec(x_147);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_57);
lean_ctor_set(x_154, 1, x_58);
x_12 = x_154;
x_13 = x_153;
goto block_18;
}
}
else
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_147);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; uint8_t x_163; lean_object* x_164; 
x_156 = lean_ctor_get(x_147, 1);
x_157 = lean_ctor_get(x_147, 0);
lean_dec(x_157);
x_158 = lean_unsigned_to_nat(1u);
x_159 = lean_mk_empty_array_with_capacity(x_158);
x_160 = lean_array_push(x_159, x_34);
x_161 = lean_box(1);
x_162 = lean_unbox(x_66);
x_163 = lean_unbox(x_161);
x_164 = l_Lean_Meta_mkForallFVars(x_160, x_58, x_162, x_25, x_163, x_59, x_60, x_61, x_62, x_156);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_160);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
lean_ctor_set(x_147, 1, x_165);
lean_ctor_set(x_147, 0, x_57);
x_12 = x_147;
x_13 = x_166;
goto block_18;
}
else
{
uint8_t x_167; 
lean_free_object(x_147);
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_167 = !lean_is_exclusive(x_164);
if (x_167 == 0)
{
return x_164;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_164, 0);
x_169 = lean_ctor_get(x_164, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_164);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; uint8_t x_177; lean_object* x_178; 
x_171 = lean_ctor_get(x_147, 1);
lean_inc(x_171);
lean_dec(x_147);
x_172 = lean_unsigned_to_nat(1u);
x_173 = lean_mk_empty_array_with_capacity(x_172);
x_174 = lean_array_push(x_173, x_34);
x_175 = lean_box(1);
x_176 = lean_unbox(x_66);
x_177 = lean_unbox(x_175);
x_178 = l_Lean_Meta_mkForallFVars(x_174, x_58, x_176, x_25, x_177, x_59, x_60, x_61, x_62, x_171);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_174);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_57);
lean_ctor_set(x_181, 1, x_179);
x_12 = x_181;
x_13 = x_180;
goto block_18;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_182 = lean_ctor_get(x_178, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_178, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_184 = x_178;
} else {
 lean_dec_ref(x_178);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
}
}
}
else
{
lean_object* x_186; uint8_t x_187; 
lean_dec(x_64);
lean_dec(x_33);
x_186 = lean_ctor_get(x_65, 0);
lean_inc(x_186);
lean_dec(x_65);
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_186, 1);
lean_dec(x_188);
x_189 = lean_ctor_get(x_186, 0);
lean_dec(x_189);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
x_190 = lean_infer_type(x_34, x_59, x_60, x_61, x_62, x_63);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
x_193 = l_Lean_Meta_matchEq_x3f(x_191, x_59, x_60, x_61, x_62, x_192);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_195);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_196;
goto block_24;
}
else
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_194);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_194, 0);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
switch (lean_obj_tag(x_200)) {
case 0:
{
lean_object* x_201; uint8_t x_202; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_201 = lean_ctor_get(x_193, 1);
lean_inc(x_201);
lean_dec(x_193);
x_202 = !lean_is_exclusive(x_198);
if (x_202 == 0)
{
lean_object* x_203; uint8_t x_204; 
x_203 = lean_ctor_get(x_198, 1);
lean_dec(x_203);
x_204 = !lean_is_exclusive(x_199);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_205 = lean_ctor_get(x_199, 0);
lean_dec(x_205);
x_206 = lean_ctor_get(x_200, 0);
lean_inc(x_206);
lean_dec(x_200);
x_207 = l_Lean_Expr_bvar___override(x_206);
lean_ctor_set(x_199, 0, x_207);
x_208 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_201);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_208;
goto block_24;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_209 = lean_ctor_get(x_199, 1);
lean_inc(x_209);
lean_dec(x_199);
x_210 = lean_ctor_get(x_200, 0);
lean_inc(x_210);
lean_dec(x_200);
x_211 = l_Lean_Expr_bvar___override(x_210);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_209);
lean_ctor_set(x_198, 1, x_212);
x_213 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_201);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_213;
goto block_24;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_214 = lean_ctor_get(x_198, 0);
lean_inc(x_214);
lean_dec(x_198);
x_215 = lean_ctor_get(x_199, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_216 = x_199;
} else {
 lean_dec_ref(x_199);
 x_216 = lean_box(0);
}
x_217 = lean_ctor_get(x_200, 0);
lean_inc(x_217);
lean_dec(x_200);
x_218 = l_Lean_Expr_bvar___override(x_217);
if (lean_is_scalar(x_216)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_216;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_215);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_214);
lean_ctor_set(x_220, 1, x_219);
lean_ctor_set(x_194, 0, x_220);
x_221 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_201);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_221;
goto block_24;
}
}
case 1:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_free_object(x_194);
lean_dec(x_198);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
x_222 = lean_ctor_get(x_193, 1);
lean_inc(x_222);
lean_dec(x_193);
x_223 = lean_ctor_get(x_199, 1);
lean_inc(x_223);
lean_dec(x_199);
x_224 = lean_ctor_get(x_200, 0);
lean_inc(x_224);
lean_dec(x_200);
lean_inc(x_224);
x_225 = l_Lean_FVarIdSet_insert(x_57, x_224);
x_226 = l_Lean_Expr_replaceFVarId(x_58, x_224, x_223);
lean_dec(x_223);
lean_dec(x_58);
lean_ctor_set(x_186, 1, x_226);
lean_ctor_set(x_186, 0, x_225);
x_12 = x_186;
x_13 = x_222;
goto block_18;
}
case 2:
{
lean_object* x_227; uint8_t x_228; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_227 = lean_ctor_get(x_193, 1);
lean_inc(x_227);
lean_dec(x_193);
x_228 = !lean_is_exclusive(x_198);
if (x_228 == 0)
{
lean_object* x_229; uint8_t x_230; 
x_229 = lean_ctor_get(x_198, 1);
lean_dec(x_229);
x_230 = !lean_is_exclusive(x_199);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_231 = lean_ctor_get(x_199, 0);
lean_dec(x_231);
x_232 = lean_ctor_get(x_200, 0);
lean_inc(x_232);
lean_dec(x_200);
x_233 = l_Lean_Expr_mvar___override(x_232);
lean_ctor_set(x_199, 0, x_233);
x_234 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_227);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_234;
goto block_24;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_235 = lean_ctor_get(x_199, 1);
lean_inc(x_235);
lean_dec(x_199);
x_236 = lean_ctor_get(x_200, 0);
lean_inc(x_236);
lean_dec(x_200);
x_237 = l_Lean_Expr_mvar___override(x_236);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_235);
lean_ctor_set(x_198, 1, x_238);
x_239 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_227);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_239;
goto block_24;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_240 = lean_ctor_get(x_198, 0);
lean_inc(x_240);
lean_dec(x_198);
x_241 = lean_ctor_get(x_199, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_242 = x_199;
} else {
 lean_dec_ref(x_199);
 x_242 = lean_box(0);
}
x_243 = lean_ctor_get(x_200, 0);
lean_inc(x_243);
lean_dec(x_200);
x_244 = l_Lean_Expr_mvar___override(x_243);
if (lean_is_scalar(x_242)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_242;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_241);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_240);
lean_ctor_set(x_246, 1, x_245);
lean_ctor_set(x_194, 0, x_246);
x_247 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_227);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_247;
goto block_24;
}
}
case 3:
{
lean_object* x_248; uint8_t x_249; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_248 = lean_ctor_get(x_193, 1);
lean_inc(x_248);
lean_dec(x_193);
x_249 = !lean_is_exclusive(x_198);
if (x_249 == 0)
{
lean_object* x_250; uint8_t x_251; 
x_250 = lean_ctor_get(x_198, 1);
lean_dec(x_250);
x_251 = !lean_is_exclusive(x_199);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_ctor_get(x_199, 0);
lean_dec(x_252);
x_253 = lean_ctor_get(x_200, 0);
lean_inc(x_253);
lean_dec(x_200);
x_254 = l_Lean_Expr_sort___override(x_253);
lean_ctor_set(x_199, 0, x_254);
x_255 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_248);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_255;
goto block_24;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_256 = lean_ctor_get(x_199, 1);
lean_inc(x_256);
lean_dec(x_199);
x_257 = lean_ctor_get(x_200, 0);
lean_inc(x_257);
lean_dec(x_200);
x_258 = l_Lean_Expr_sort___override(x_257);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_256);
lean_ctor_set(x_198, 1, x_259);
x_260 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_248);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_260;
goto block_24;
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_261 = lean_ctor_get(x_198, 0);
lean_inc(x_261);
lean_dec(x_198);
x_262 = lean_ctor_get(x_199, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_263 = x_199;
} else {
 lean_dec_ref(x_199);
 x_263 = lean_box(0);
}
x_264 = lean_ctor_get(x_200, 0);
lean_inc(x_264);
lean_dec(x_200);
x_265 = l_Lean_Expr_sort___override(x_264);
if (lean_is_scalar(x_263)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_263;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_262);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_261);
lean_ctor_set(x_267, 1, x_266);
lean_ctor_set(x_194, 0, x_267);
x_268 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_248);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_268;
goto block_24;
}
}
case 4:
{
lean_object* x_269; uint8_t x_270; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_269 = lean_ctor_get(x_193, 1);
lean_inc(x_269);
lean_dec(x_193);
x_270 = !lean_is_exclusive(x_198);
if (x_270 == 0)
{
lean_object* x_271; uint8_t x_272; 
x_271 = lean_ctor_get(x_198, 1);
lean_dec(x_271);
x_272 = !lean_is_exclusive(x_199);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_273 = lean_ctor_get(x_199, 0);
lean_dec(x_273);
x_274 = lean_ctor_get(x_200, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_200, 1);
lean_inc(x_275);
lean_dec(x_200);
x_276 = l_Lean_Expr_const___override(x_274, x_275);
lean_ctor_set(x_199, 0, x_276);
x_277 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_269);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_277;
goto block_24;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_278 = lean_ctor_get(x_199, 1);
lean_inc(x_278);
lean_dec(x_199);
x_279 = lean_ctor_get(x_200, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_200, 1);
lean_inc(x_280);
lean_dec(x_200);
x_281 = l_Lean_Expr_const___override(x_279, x_280);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_278);
lean_ctor_set(x_198, 1, x_282);
x_283 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_269);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_283;
goto block_24;
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_284 = lean_ctor_get(x_198, 0);
lean_inc(x_284);
lean_dec(x_198);
x_285 = lean_ctor_get(x_199, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_286 = x_199;
} else {
 lean_dec_ref(x_199);
 x_286 = lean_box(0);
}
x_287 = lean_ctor_get(x_200, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_200, 1);
lean_inc(x_288);
lean_dec(x_200);
x_289 = l_Lean_Expr_const___override(x_287, x_288);
if (lean_is_scalar(x_286)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_286;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_285);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_284);
lean_ctor_set(x_291, 1, x_290);
lean_ctor_set(x_194, 0, x_291);
x_292 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_269);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_292;
goto block_24;
}
}
case 5:
{
lean_object* x_293; uint8_t x_294; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_293 = lean_ctor_get(x_193, 1);
lean_inc(x_293);
lean_dec(x_193);
x_294 = !lean_is_exclusive(x_198);
if (x_294 == 0)
{
lean_object* x_295; uint8_t x_296; 
x_295 = lean_ctor_get(x_198, 1);
lean_dec(x_295);
x_296 = !lean_is_exclusive(x_199);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_297 = lean_ctor_get(x_199, 0);
lean_dec(x_297);
x_298 = lean_ctor_get(x_200, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_200, 1);
lean_inc(x_299);
lean_dec(x_200);
x_300 = l_Lean_Expr_app___override(x_298, x_299);
lean_ctor_set(x_199, 0, x_300);
x_301 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_293);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_301;
goto block_24;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_302 = lean_ctor_get(x_199, 1);
lean_inc(x_302);
lean_dec(x_199);
x_303 = lean_ctor_get(x_200, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_200, 1);
lean_inc(x_304);
lean_dec(x_200);
x_305 = l_Lean_Expr_app___override(x_303, x_304);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_302);
lean_ctor_set(x_198, 1, x_306);
x_307 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_293);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_307;
goto block_24;
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_308 = lean_ctor_get(x_198, 0);
lean_inc(x_308);
lean_dec(x_198);
x_309 = lean_ctor_get(x_199, 1);
lean_inc(x_309);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_310 = x_199;
} else {
 lean_dec_ref(x_199);
 x_310 = lean_box(0);
}
x_311 = lean_ctor_get(x_200, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_200, 1);
lean_inc(x_312);
lean_dec(x_200);
x_313 = l_Lean_Expr_app___override(x_311, x_312);
if (lean_is_scalar(x_310)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_310;
}
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_309);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_308);
lean_ctor_set(x_315, 1, x_314);
lean_ctor_set(x_194, 0, x_315);
x_316 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_293);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_316;
goto block_24;
}
}
case 6:
{
lean_object* x_317; uint8_t x_318; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_317 = lean_ctor_get(x_193, 1);
lean_inc(x_317);
lean_dec(x_193);
x_318 = !lean_is_exclusive(x_198);
if (x_318 == 0)
{
lean_object* x_319; uint8_t x_320; 
x_319 = lean_ctor_get(x_198, 1);
lean_dec(x_319);
x_320 = !lean_is_exclusive(x_199);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; lean_object* x_326; lean_object* x_327; 
x_321 = lean_ctor_get(x_199, 0);
lean_dec(x_321);
x_322 = lean_ctor_get(x_200, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_200, 1);
lean_inc(x_323);
x_324 = lean_ctor_get(x_200, 2);
lean_inc(x_324);
x_325 = lean_ctor_get_uint8(x_200, sizeof(void*)*3 + 8);
lean_dec(x_200);
x_326 = l_Lean_Expr_lam___override(x_322, x_323, x_324, x_325);
lean_ctor_set(x_199, 0, x_326);
x_327 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_317);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_327;
goto block_24;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_328 = lean_ctor_get(x_199, 1);
lean_inc(x_328);
lean_dec(x_199);
x_329 = lean_ctor_get(x_200, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_200, 1);
lean_inc(x_330);
x_331 = lean_ctor_get(x_200, 2);
lean_inc(x_331);
x_332 = lean_ctor_get_uint8(x_200, sizeof(void*)*3 + 8);
lean_dec(x_200);
x_333 = l_Lean_Expr_lam___override(x_329, x_330, x_331, x_332);
x_334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_328);
lean_ctor_set(x_198, 1, x_334);
x_335 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_317);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_335;
goto block_24;
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_336 = lean_ctor_get(x_198, 0);
lean_inc(x_336);
lean_dec(x_198);
x_337 = lean_ctor_get(x_199, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_338 = x_199;
} else {
 lean_dec_ref(x_199);
 x_338 = lean_box(0);
}
x_339 = lean_ctor_get(x_200, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_200, 1);
lean_inc(x_340);
x_341 = lean_ctor_get(x_200, 2);
lean_inc(x_341);
x_342 = lean_ctor_get_uint8(x_200, sizeof(void*)*3 + 8);
lean_dec(x_200);
x_343 = l_Lean_Expr_lam___override(x_339, x_340, x_341, x_342);
if (lean_is_scalar(x_338)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_338;
}
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_337);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_336);
lean_ctor_set(x_345, 1, x_344);
lean_ctor_set(x_194, 0, x_345);
x_346 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_317);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_346;
goto block_24;
}
}
case 7:
{
lean_object* x_347; uint8_t x_348; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_347 = lean_ctor_get(x_193, 1);
lean_inc(x_347);
lean_dec(x_193);
x_348 = !lean_is_exclusive(x_198);
if (x_348 == 0)
{
lean_object* x_349; uint8_t x_350; 
x_349 = lean_ctor_get(x_198, 1);
lean_dec(x_349);
x_350 = !lean_is_exclusive(x_199);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; lean_object* x_357; 
x_351 = lean_ctor_get(x_199, 0);
lean_dec(x_351);
x_352 = lean_ctor_get(x_200, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_200, 1);
lean_inc(x_353);
x_354 = lean_ctor_get(x_200, 2);
lean_inc(x_354);
x_355 = lean_ctor_get_uint8(x_200, sizeof(void*)*3 + 8);
lean_dec(x_200);
x_356 = l_Lean_Expr_forallE___override(x_352, x_353, x_354, x_355);
lean_ctor_set(x_199, 0, x_356);
x_357 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_347);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_357;
goto block_24;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_358 = lean_ctor_get(x_199, 1);
lean_inc(x_358);
lean_dec(x_199);
x_359 = lean_ctor_get(x_200, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_200, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_200, 2);
lean_inc(x_361);
x_362 = lean_ctor_get_uint8(x_200, sizeof(void*)*3 + 8);
lean_dec(x_200);
x_363 = l_Lean_Expr_forallE___override(x_359, x_360, x_361, x_362);
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_358);
lean_ctor_set(x_198, 1, x_364);
x_365 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_347);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_365;
goto block_24;
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_366 = lean_ctor_get(x_198, 0);
lean_inc(x_366);
lean_dec(x_198);
x_367 = lean_ctor_get(x_199, 1);
lean_inc(x_367);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_368 = x_199;
} else {
 lean_dec_ref(x_199);
 x_368 = lean_box(0);
}
x_369 = lean_ctor_get(x_200, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_200, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_200, 2);
lean_inc(x_371);
x_372 = lean_ctor_get_uint8(x_200, sizeof(void*)*3 + 8);
lean_dec(x_200);
x_373 = l_Lean_Expr_forallE___override(x_369, x_370, x_371, x_372);
if (lean_is_scalar(x_368)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_368;
}
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_367);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_366);
lean_ctor_set(x_375, 1, x_374);
lean_ctor_set(x_194, 0, x_375);
x_376 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_347);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_376;
goto block_24;
}
}
case 8:
{
lean_object* x_377; uint8_t x_378; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_377 = lean_ctor_get(x_193, 1);
lean_inc(x_377);
lean_dec(x_193);
x_378 = !lean_is_exclusive(x_198);
if (x_378 == 0)
{
lean_object* x_379; uint8_t x_380; 
x_379 = lean_ctor_get(x_198, 1);
lean_dec(x_379);
x_380 = !lean_is_exclusive(x_199);
if (x_380 == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; uint8_t x_386; lean_object* x_387; lean_object* x_388; 
x_381 = lean_ctor_get(x_199, 0);
lean_dec(x_381);
x_382 = lean_ctor_get(x_200, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_200, 1);
lean_inc(x_383);
x_384 = lean_ctor_get(x_200, 2);
lean_inc(x_384);
x_385 = lean_ctor_get(x_200, 3);
lean_inc(x_385);
x_386 = lean_ctor_get_uint8(x_200, sizeof(void*)*4 + 8);
lean_dec(x_200);
x_387 = l_Lean_Expr_letE___override(x_382, x_383, x_384, x_385, x_386);
lean_ctor_set(x_199, 0, x_387);
x_388 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_377);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_388;
goto block_24;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_389 = lean_ctor_get(x_199, 1);
lean_inc(x_389);
lean_dec(x_199);
x_390 = lean_ctor_get(x_200, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_200, 1);
lean_inc(x_391);
x_392 = lean_ctor_get(x_200, 2);
lean_inc(x_392);
x_393 = lean_ctor_get(x_200, 3);
lean_inc(x_393);
x_394 = lean_ctor_get_uint8(x_200, sizeof(void*)*4 + 8);
lean_dec(x_200);
x_395 = l_Lean_Expr_letE___override(x_390, x_391, x_392, x_393, x_394);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_389);
lean_ctor_set(x_198, 1, x_396);
x_397 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_377);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_397;
goto block_24;
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_398 = lean_ctor_get(x_198, 0);
lean_inc(x_398);
lean_dec(x_198);
x_399 = lean_ctor_get(x_199, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_400 = x_199;
} else {
 lean_dec_ref(x_199);
 x_400 = lean_box(0);
}
x_401 = lean_ctor_get(x_200, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_200, 1);
lean_inc(x_402);
x_403 = lean_ctor_get(x_200, 2);
lean_inc(x_403);
x_404 = lean_ctor_get(x_200, 3);
lean_inc(x_404);
x_405 = lean_ctor_get_uint8(x_200, sizeof(void*)*4 + 8);
lean_dec(x_200);
x_406 = l_Lean_Expr_letE___override(x_401, x_402, x_403, x_404, x_405);
if (lean_is_scalar(x_400)) {
 x_407 = lean_alloc_ctor(0, 2, 0);
} else {
 x_407 = x_400;
}
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_399);
x_408 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_408, 0, x_398);
lean_ctor_set(x_408, 1, x_407);
lean_ctor_set(x_194, 0, x_408);
x_409 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_377);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_409;
goto block_24;
}
}
case 9:
{
lean_object* x_410; uint8_t x_411; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_410 = lean_ctor_get(x_193, 1);
lean_inc(x_410);
lean_dec(x_193);
x_411 = !lean_is_exclusive(x_198);
if (x_411 == 0)
{
lean_object* x_412; uint8_t x_413; 
x_412 = lean_ctor_get(x_198, 1);
lean_dec(x_412);
x_413 = !lean_is_exclusive(x_199);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_414 = lean_ctor_get(x_199, 0);
lean_dec(x_414);
x_415 = lean_ctor_get(x_200, 0);
lean_inc(x_415);
lean_dec(x_200);
x_416 = l_Lean_Expr_lit___override(x_415);
lean_ctor_set(x_199, 0, x_416);
x_417 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_410);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_417;
goto block_24;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_418 = lean_ctor_get(x_199, 1);
lean_inc(x_418);
lean_dec(x_199);
x_419 = lean_ctor_get(x_200, 0);
lean_inc(x_419);
lean_dec(x_200);
x_420 = l_Lean_Expr_lit___override(x_419);
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_418);
lean_ctor_set(x_198, 1, x_421);
x_422 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_410);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_422;
goto block_24;
}
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_423 = lean_ctor_get(x_198, 0);
lean_inc(x_423);
lean_dec(x_198);
x_424 = lean_ctor_get(x_199, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_425 = x_199;
} else {
 lean_dec_ref(x_199);
 x_425 = lean_box(0);
}
x_426 = lean_ctor_get(x_200, 0);
lean_inc(x_426);
lean_dec(x_200);
x_427 = l_Lean_Expr_lit___override(x_426);
if (lean_is_scalar(x_425)) {
 x_428 = lean_alloc_ctor(0, 2, 0);
} else {
 x_428 = x_425;
}
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_424);
x_429 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_429, 0, x_423);
lean_ctor_set(x_429, 1, x_428);
lean_ctor_set(x_194, 0, x_429);
x_430 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_410);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_430;
goto block_24;
}
}
case 10:
{
lean_object* x_431; uint8_t x_432; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_431 = lean_ctor_get(x_193, 1);
lean_inc(x_431);
lean_dec(x_193);
x_432 = !lean_is_exclusive(x_198);
if (x_432 == 0)
{
lean_object* x_433; uint8_t x_434; 
x_433 = lean_ctor_get(x_198, 1);
lean_dec(x_433);
x_434 = !lean_is_exclusive(x_199);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_435 = lean_ctor_get(x_199, 0);
lean_dec(x_435);
x_436 = lean_ctor_get(x_200, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_200, 1);
lean_inc(x_437);
lean_dec(x_200);
x_438 = l_Lean_Expr_mdata___override(x_436, x_437);
lean_ctor_set(x_199, 0, x_438);
x_439 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_431);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_439;
goto block_24;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_440 = lean_ctor_get(x_199, 1);
lean_inc(x_440);
lean_dec(x_199);
x_441 = lean_ctor_get(x_200, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_200, 1);
lean_inc(x_442);
lean_dec(x_200);
x_443 = l_Lean_Expr_mdata___override(x_441, x_442);
x_444 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_440);
lean_ctor_set(x_198, 1, x_444);
x_445 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_431);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_445;
goto block_24;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_446 = lean_ctor_get(x_198, 0);
lean_inc(x_446);
lean_dec(x_198);
x_447 = lean_ctor_get(x_199, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_448 = x_199;
} else {
 lean_dec_ref(x_199);
 x_448 = lean_box(0);
}
x_449 = lean_ctor_get(x_200, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_200, 1);
lean_inc(x_450);
lean_dec(x_200);
x_451 = l_Lean_Expr_mdata___override(x_449, x_450);
if (lean_is_scalar(x_448)) {
 x_452 = lean_alloc_ctor(0, 2, 0);
} else {
 x_452 = x_448;
}
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_447);
x_453 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_453, 0, x_446);
lean_ctor_set(x_453, 1, x_452);
lean_ctor_set(x_194, 0, x_453);
x_454 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_431);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_454;
goto block_24;
}
}
default: 
{
lean_object* x_455; uint8_t x_456; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_455 = lean_ctor_get(x_193, 1);
lean_inc(x_455);
lean_dec(x_193);
x_456 = !lean_is_exclusive(x_198);
if (x_456 == 0)
{
lean_object* x_457; uint8_t x_458; 
x_457 = lean_ctor_get(x_198, 1);
lean_dec(x_457);
x_458 = !lean_is_exclusive(x_199);
if (x_458 == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_459 = lean_ctor_get(x_199, 0);
lean_dec(x_459);
x_460 = lean_ctor_get(x_200, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_200, 1);
lean_inc(x_461);
x_462 = lean_ctor_get(x_200, 2);
lean_inc(x_462);
lean_dec(x_200);
x_463 = l_Lean_Expr_proj___override(x_460, x_461, x_462);
lean_ctor_set(x_199, 0, x_463);
x_464 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_455);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_464;
goto block_24;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_465 = lean_ctor_get(x_199, 1);
lean_inc(x_465);
lean_dec(x_199);
x_466 = lean_ctor_get(x_200, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_200, 1);
lean_inc(x_467);
x_468 = lean_ctor_get(x_200, 2);
lean_inc(x_468);
lean_dec(x_200);
x_469 = l_Lean_Expr_proj___override(x_466, x_467, x_468);
x_470 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_470, 0, x_469);
lean_ctor_set(x_470, 1, x_465);
lean_ctor_set(x_198, 1, x_470);
x_471 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_455);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_471;
goto block_24;
}
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_472 = lean_ctor_get(x_198, 0);
lean_inc(x_472);
lean_dec(x_198);
x_473 = lean_ctor_get(x_199, 1);
lean_inc(x_473);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_474 = x_199;
} else {
 lean_dec_ref(x_199);
 x_474 = lean_box(0);
}
x_475 = lean_ctor_get(x_200, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_200, 1);
lean_inc(x_476);
x_477 = lean_ctor_get(x_200, 2);
lean_inc(x_477);
lean_dec(x_200);
x_478 = l_Lean_Expr_proj___override(x_475, x_476, x_477);
if (lean_is_scalar(x_474)) {
 x_479 = lean_alloc_ctor(0, 2, 0);
} else {
 x_479 = x_474;
}
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_473);
x_480 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_480, 0, x_472);
lean_ctor_set(x_480, 1, x_479);
lean_ctor_set(x_194, 0, x_480);
x_481 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_455);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_481;
goto block_24;
}
}
}
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_194, 0);
lean_inc(x_482);
lean_dec(x_194);
x_483 = lean_ctor_get(x_482, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_483, 0);
lean_inc(x_484);
switch (lean_obj_tag(x_484)) {
case 0:
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_485 = lean_ctor_get(x_193, 1);
lean_inc(x_485);
lean_dec(x_193);
x_486 = lean_ctor_get(x_482, 0);
lean_inc(x_486);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_487 = x_482;
} else {
 lean_dec_ref(x_482);
 x_487 = lean_box(0);
}
x_488 = lean_ctor_get(x_483, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_489 = x_483;
} else {
 lean_dec_ref(x_483);
 x_489 = lean_box(0);
}
x_490 = lean_ctor_get(x_484, 0);
lean_inc(x_490);
lean_dec(x_484);
x_491 = l_Lean_Expr_bvar___override(x_490);
if (lean_is_scalar(x_489)) {
 x_492 = lean_alloc_ctor(0, 2, 0);
} else {
 x_492 = x_489;
}
lean_ctor_set(x_492, 0, x_491);
lean_ctor_set(x_492, 1, x_488);
if (lean_is_scalar(x_487)) {
 x_493 = lean_alloc_ctor(0, 2, 0);
} else {
 x_493 = x_487;
}
lean_ctor_set(x_493, 0, x_486);
lean_ctor_set(x_493, 1, x_492);
x_494 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_494, 0, x_493);
x_495 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_494, x_59, x_60, x_61, x_62, x_485);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_494);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_495;
goto block_24;
}
case 1:
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_482);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
x_496 = lean_ctor_get(x_193, 1);
lean_inc(x_496);
lean_dec(x_193);
x_497 = lean_ctor_get(x_483, 1);
lean_inc(x_497);
lean_dec(x_483);
x_498 = lean_ctor_get(x_484, 0);
lean_inc(x_498);
lean_dec(x_484);
lean_inc(x_498);
x_499 = l_Lean_FVarIdSet_insert(x_57, x_498);
x_500 = l_Lean_Expr_replaceFVarId(x_58, x_498, x_497);
lean_dec(x_497);
lean_dec(x_58);
lean_ctor_set(x_186, 1, x_500);
lean_ctor_set(x_186, 0, x_499);
x_12 = x_186;
x_13 = x_496;
goto block_18;
}
case 2:
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_501 = lean_ctor_get(x_193, 1);
lean_inc(x_501);
lean_dec(x_193);
x_502 = lean_ctor_get(x_482, 0);
lean_inc(x_502);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_503 = x_482;
} else {
 lean_dec_ref(x_482);
 x_503 = lean_box(0);
}
x_504 = lean_ctor_get(x_483, 1);
lean_inc(x_504);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_505 = x_483;
} else {
 lean_dec_ref(x_483);
 x_505 = lean_box(0);
}
x_506 = lean_ctor_get(x_484, 0);
lean_inc(x_506);
lean_dec(x_484);
x_507 = l_Lean_Expr_mvar___override(x_506);
if (lean_is_scalar(x_505)) {
 x_508 = lean_alloc_ctor(0, 2, 0);
} else {
 x_508 = x_505;
}
lean_ctor_set(x_508, 0, x_507);
lean_ctor_set(x_508, 1, x_504);
if (lean_is_scalar(x_503)) {
 x_509 = lean_alloc_ctor(0, 2, 0);
} else {
 x_509 = x_503;
}
lean_ctor_set(x_509, 0, x_502);
lean_ctor_set(x_509, 1, x_508);
x_510 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_510, 0, x_509);
x_511 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_510, x_59, x_60, x_61, x_62, x_501);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_510);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_511;
goto block_24;
}
case 3:
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_512 = lean_ctor_get(x_193, 1);
lean_inc(x_512);
lean_dec(x_193);
x_513 = lean_ctor_get(x_482, 0);
lean_inc(x_513);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_514 = x_482;
} else {
 lean_dec_ref(x_482);
 x_514 = lean_box(0);
}
x_515 = lean_ctor_get(x_483, 1);
lean_inc(x_515);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_516 = x_483;
} else {
 lean_dec_ref(x_483);
 x_516 = lean_box(0);
}
x_517 = lean_ctor_get(x_484, 0);
lean_inc(x_517);
lean_dec(x_484);
x_518 = l_Lean_Expr_sort___override(x_517);
if (lean_is_scalar(x_516)) {
 x_519 = lean_alloc_ctor(0, 2, 0);
} else {
 x_519 = x_516;
}
lean_ctor_set(x_519, 0, x_518);
lean_ctor_set(x_519, 1, x_515);
if (lean_is_scalar(x_514)) {
 x_520 = lean_alloc_ctor(0, 2, 0);
} else {
 x_520 = x_514;
}
lean_ctor_set(x_520, 0, x_513);
lean_ctor_set(x_520, 1, x_519);
x_521 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_521, 0, x_520);
x_522 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_521, x_59, x_60, x_61, x_62, x_512);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_521);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_522;
goto block_24;
}
case 4:
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_523 = lean_ctor_get(x_193, 1);
lean_inc(x_523);
lean_dec(x_193);
x_524 = lean_ctor_get(x_482, 0);
lean_inc(x_524);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_525 = x_482;
} else {
 lean_dec_ref(x_482);
 x_525 = lean_box(0);
}
x_526 = lean_ctor_get(x_483, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_527 = x_483;
} else {
 lean_dec_ref(x_483);
 x_527 = lean_box(0);
}
x_528 = lean_ctor_get(x_484, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_484, 1);
lean_inc(x_529);
lean_dec(x_484);
x_530 = l_Lean_Expr_const___override(x_528, x_529);
if (lean_is_scalar(x_527)) {
 x_531 = lean_alloc_ctor(0, 2, 0);
} else {
 x_531 = x_527;
}
lean_ctor_set(x_531, 0, x_530);
lean_ctor_set(x_531, 1, x_526);
if (lean_is_scalar(x_525)) {
 x_532 = lean_alloc_ctor(0, 2, 0);
} else {
 x_532 = x_525;
}
lean_ctor_set(x_532, 0, x_524);
lean_ctor_set(x_532, 1, x_531);
x_533 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_533, 0, x_532);
x_534 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_533, x_59, x_60, x_61, x_62, x_523);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_533);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_534;
goto block_24;
}
case 5:
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_535 = lean_ctor_get(x_193, 1);
lean_inc(x_535);
lean_dec(x_193);
x_536 = lean_ctor_get(x_482, 0);
lean_inc(x_536);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_537 = x_482;
} else {
 lean_dec_ref(x_482);
 x_537 = lean_box(0);
}
x_538 = lean_ctor_get(x_483, 1);
lean_inc(x_538);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_539 = x_483;
} else {
 lean_dec_ref(x_483);
 x_539 = lean_box(0);
}
x_540 = lean_ctor_get(x_484, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_484, 1);
lean_inc(x_541);
lean_dec(x_484);
x_542 = l_Lean_Expr_app___override(x_540, x_541);
if (lean_is_scalar(x_539)) {
 x_543 = lean_alloc_ctor(0, 2, 0);
} else {
 x_543 = x_539;
}
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_538);
if (lean_is_scalar(x_537)) {
 x_544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_544 = x_537;
}
lean_ctor_set(x_544, 0, x_536);
lean_ctor_set(x_544, 1, x_543);
x_545 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_545, 0, x_544);
x_546 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_545, x_59, x_60, x_61, x_62, x_535);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_545);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_546;
goto block_24;
}
case 6:
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; uint8_t x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_547 = lean_ctor_get(x_193, 1);
lean_inc(x_547);
lean_dec(x_193);
x_548 = lean_ctor_get(x_482, 0);
lean_inc(x_548);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_549 = x_482;
} else {
 lean_dec_ref(x_482);
 x_549 = lean_box(0);
}
x_550 = lean_ctor_get(x_483, 1);
lean_inc(x_550);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_551 = x_483;
} else {
 lean_dec_ref(x_483);
 x_551 = lean_box(0);
}
x_552 = lean_ctor_get(x_484, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_484, 1);
lean_inc(x_553);
x_554 = lean_ctor_get(x_484, 2);
lean_inc(x_554);
x_555 = lean_ctor_get_uint8(x_484, sizeof(void*)*3 + 8);
lean_dec(x_484);
x_556 = l_Lean_Expr_lam___override(x_552, x_553, x_554, x_555);
if (lean_is_scalar(x_551)) {
 x_557 = lean_alloc_ctor(0, 2, 0);
} else {
 x_557 = x_551;
}
lean_ctor_set(x_557, 0, x_556);
lean_ctor_set(x_557, 1, x_550);
if (lean_is_scalar(x_549)) {
 x_558 = lean_alloc_ctor(0, 2, 0);
} else {
 x_558 = x_549;
}
lean_ctor_set(x_558, 0, x_548);
lean_ctor_set(x_558, 1, x_557);
x_559 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_559, 0, x_558);
x_560 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_559, x_59, x_60, x_61, x_62, x_547);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_559);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_560;
goto block_24;
}
case 7:
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; uint8_t x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_561 = lean_ctor_get(x_193, 1);
lean_inc(x_561);
lean_dec(x_193);
x_562 = lean_ctor_get(x_482, 0);
lean_inc(x_562);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_563 = x_482;
} else {
 lean_dec_ref(x_482);
 x_563 = lean_box(0);
}
x_564 = lean_ctor_get(x_483, 1);
lean_inc(x_564);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_565 = x_483;
} else {
 lean_dec_ref(x_483);
 x_565 = lean_box(0);
}
x_566 = lean_ctor_get(x_484, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_484, 1);
lean_inc(x_567);
x_568 = lean_ctor_get(x_484, 2);
lean_inc(x_568);
x_569 = lean_ctor_get_uint8(x_484, sizeof(void*)*3 + 8);
lean_dec(x_484);
x_570 = l_Lean_Expr_forallE___override(x_566, x_567, x_568, x_569);
if (lean_is_scalar(x_565)) {
 x_571 = lean_alloc_ctor(0, 2, 0);
} else {
 x_571 = x_565;
}
lean_ctor_set(x_571, 0, x_570);
lean_ctor_set(x_571, 1, x_564);
if (lean_is_scalar(x_563)) {
 x_572 = lean_alloc_ctor(0, 2, 0);
} else {
 x_572 = x_563;
}
lean_ctor_set(x_572, 0, x_562);
lean_ctor_set(x_572, 1, x_571);
x_573 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_573, 0, x_572);
x_574 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_573, x_59, x_60, x_61, x_62, x_561);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_573);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_574;
goto block_24;
}
case 8:
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; uint8_t x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_575 = lean_ctor_get(x_193, 1);
lean_inc(x_575);
lean_dec(x_193);
x_576 = lean_ctor_get(x_482, 0);
lean_inc(x_576);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_577 = x_482;
} else {
 lean_dec_ref(x_482);
 x_577 = lean_box(0);
}
x_578 = lean_ctor_get(x_483, 1);
lean_inc(x_578);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_579 = x_483;
} else {
 lean_dec_ref(x_483);
 x_579 = lean_box(0);
}
x_580 = lean_ctor_get(x_484, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_484, 1);
lean_inc(x_581);
x_582 = lean_ctor_get(x_484, 2);
lean_inc(x_582);
x_583 = lean_ctor_get(x_484, 3);
lean_inc(x_583);
x_584 = lean_ctor_get_uint8(x_484, sizeof(void*)*4 + 8);
lean_dec(x_484);
x_585 = l_Lean_Expr_letE___override(x_580, x_581, x_582, x_583, x_584);
if (lean_is_scalar(x_579)) {
 x_586 = lean_alloc_ctor(0, 2, 0);
} else {
 x_586 = x_579;
}
lean_ctor_set(x_586, 0, x_585);
lean_ctor_set(x_586, 1, x_578);
if (lean_is_scalar(x_577)) {
 x_587 = lean_alloc_ctor(0, 2, 0);
} else {
 x_587 = x_577;
}
lean_ctor_set(x_587, 0, x_576);
lean_ctor_set(x_587, 1, x_586);
x_588 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_588, 0, x_587);
x_589 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_588, x_59, x_60, x_61, x_62, x_575);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_588);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_589;
goto block_24;
}
case 9:
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_590 = lean_ctor_get(x_193, 1);
lean_inc(x_590);
lean_dec(x_193);
x_591 = lean_ctor_get(x_482, 0);
lean_inc(x_591);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_592 = x_482;
} else {
 lean_dec_ref(x_482);
 x_592 = lean_box(0);
}
x_593 = lean_ctor_get(x_483, 1);
lean_inc(x_593);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_594 = x_483;
} else {
 lean_dec_ref(x_483);
 x_594 = lean_box(0);
}
x_595 = lean_ctor_get(x_484, 0);
lean_inc(x_595);
lean_dec(x_484);
x_596 = l_Lean_Expr_lit___override(x_595);
if (lean_is_scalar(x_594)) {
 x_597 = lean_alloc_ctor(0, 2, 0);
} else {
 x_597 = x_594;
}
lean_ctor_set(x_597, 0, x_596);
lean_ctor_set(x_597, 1, x_593);
if (lean_is_scalar(x_592)) {
 x_598 = lean_alloc_ctor(0, 2, 0);
} else {
 x_598 = x_592;
}
lean_ctor_set(x_598, 0, x_591);
lean_ctor_set(x_598, 1, x_597);
x_599 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_599, 0, x_598);
x_600 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_599, x_59, x_60, x_61, x_62, x_590);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_599);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_600;
goto block_24;
}
case 10:
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_601 = lean_ctor_get(x_193, 1);
lean_inc(x_601);
lean_dec(x_193);
x_602 = lean_ctor_get(x_482, 0);
lean_inc(x_602);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_603 = x_482;
} else {
 lean_dec_ref(x_482);
 x_603 = lean_box(0);
}
x_604 = lean_ctor_get(x_483, 1);
lean_inc(x_604);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_605 = x_483;
} else {
 lean_dec_ref(x_483);
 x_605 = lean_box(0);
}
x_606 = lean_ctor_get(x_484, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_484, 1);
lean_inc(x_607);
lean_dec(x_484);
x_608 = l_Lean_Expr_mdata___override(x_606, x_607);
if (lean_is_scalar(x_605)) {
 x_609 = lean_alloc_ctor(0, 2, 0);
} else {
 x_609 = x_605;
}
lean_ctor_set(x_609, 0, x_608);
lean_ctor_set(x_609, 1, x_604);
if (lean_is_scalar(x_603)) {
 x_610 = lean_alloc_ctor(0, 2, 0);
} else {
 x_610 = x_603;
}
lean_ctor_set(x_610, 0, x_602);
lean_ctor_set(x_610, 1, x_609);
x_611 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_611, 0, x_610);
x_612 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_611, x_59, x_60, x_61, x_62, x_601);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_611);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_612;
goto block_24;
}
default: 
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_613 = lean_ctor_get(x_193, 1);
lean_inc(x_613);
lean_dec(x_193);
x_614 = lean_ctor_get(x_482, 0);
lean_inc(x_614);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_615 = x_482;
} else {
 lean_dec_ref(x_482);
 x_615 = lean_box(0);
}
x_616 = lean_ctor_get(x_483, 1);
lean_inc(x_616);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_617 = x_483;
} else {
 lean_dec_ref(x_483);
 x_617 = lean_box(0);
}
x_618 = lean_ctor_get(x_484, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_484, 1);
lean_inc(x_619);
x_620 = lean_ctor_get(x_484, 2);
lean_inc(x_620);
lean_dec(x_484);
x_621 = l_Lean_Expr_proj___override(x_618, x_619, x_620);
if (lean_is_scalar(x_617)) {
 x_622 = lean_alloc_ctor(0, 2, 0);
} else {
 x_622 = x_617;
}
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_616);
if (lean_is_scalar(x_615)) {
 x_623 = lean_alloc_ctor(0, 2, 0);
} else {
 x_623 = x_615;
}
lean_ctor_set(x_623, 0, x_614);
lean_ctor_set(x_623, 1, x_622);
x_624 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_624, 0, x_623);
x_625 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_624, x_59, x_60, x_61, x_62, x_613);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_624);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_625;
goto block_24;
}
}
}
}
}
else
{
uint8_t x_626; 
lean_free_object(x_186);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_626 = !lean_is_exclusive(x_193);
if (x_626 == 0)
{
return x_193;
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; 
x_627 = lean_ctor_get(x_193, 0);
x_628 = lean_ctor_get(x_193, 1);
lean_inc(x_628);
lean_inc(x_627);
lean_dec(x_193);
x_629 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_629, 0, x_627);
lean_ctor_set(x_629, 1, x_628);
return x_629;
}
}
}
else
{
uint8_t x_630; 
lean_free_object(x_186);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_630 = !lean_is_exclusive(x_190);
if (x_630 == 0)
{
return x_190;
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_631 = lean_ctor_get(x_190, 0);
x_632 = lean_ctor_get(x_190, 1);
lean_inc(x_632);
lean_inc(x_631);
lean_dec(x_190);
x_633 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_633, 0, x_631);
lean_ctor_set(x_633, 1, x_632);
return x_633;
}
}
}
else
{
lean_object* x_634; 
lean_dec(x_186);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
x_634 = lean_infer_type(x_34, x_59, x_60, x_61, x_62, x_63);
if (lean_obj_tag(x_634) == 0)
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_635 = lean_ctor_get(x_634, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_634, 1);
lean_inc(x_636);
lean_dec(x_634);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
x_637 = l_Lean_Meta_matchEq_x3f(x_635, x_59, x_60, x_61, x_62, x_636);
if (lean_obj_tag(x_637) == 0)
{
lean_object* x_638; 
x_638 = lean_ctor_get(x_637, 0);
lean_inc(x_638);
if (lean_obj_tag(x_638) == 0)
{
lean_object* x_639; lean_object* x_640; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_639 = lean_ctor_get(x_637, 1);
lean_inc(x_639);
lean_dec(x_637);
x_640 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_638, x_59, x_60, x_61, x_62, x_639);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_640;
goto block_24;
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_641 = lean_ctor_get(x_638, 0);
lean_inc(x_641);
if (lean_is_exclusive(x_638)) {
 lean_ctor_release(x_638, 0);
 x_642 = x_638;
} else {
 lean_dec_ref(x_638);
 x_642 = lean_box(0);
}
x_643 = lean_ctor_get(x_641, 1);
lean_inc(x_643);
x_644 = lean_ctor_get(x_643, 0);
lean_inc(x_644);
switch (lean_obj_tag(x_644)) {
case 0:
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_645 = lean_ctor_get(x_637, 1);
lean_inc(x_645);
lean_dec(x_637);
x_646 = lean_ctor_get(x_641, 0);
lean_inc(x_646);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_647 = x_641;
} else {
 lean_dec_ref(x_641);
 x_647 = lean_box(0);
}
x_648 = lean_ctor_get(x_643, 1);
lean_inc(x_648);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_649 = x_643;
} else {
 lean_dec_ref(x_643);
 x_649 = lean_box(0);
}
x_650 = lean_ctor_get(x_644, 0);
lean_inc(x_650);
lean_dec(x_644);
x_651 = l_Lean_Expr_bvar___override(x_650);
if (lean_is_scalar(x_649)) {
 x_652 = lean_alloc_ctor(0, 2, 0);
} else {
 x_652 = x_649;
}
lean_ctor_set(x_652, 0, x_651);
lean_ctor_set(x_652, 1, x_648);
if (lean_is_scalar(x_647)) {
 x_653 = lean_alloc_ctor(0, 2, 0);
} else {
 x_653 = x_647;
}
lean_ctor_set(x_653, 0, x_646);
lean_ctor_set(x_653, 1, x_652);
if (lean_is_scalar(x_642)) {
 x_654 = lean_alloc_ctor(1, 1, 0);
} else {
 x_654 = x_642;
}
lean_ctor_set(x_654, 0, x_653);
x_655 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_654, x_59, x_60, x_61, x_62, x_645);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_654);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_655;
goto block_24;
}
case 1:
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_642);
lean_dec(x_641);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
x_656 = lean_ctor_get(x_637, 1);
lean_inc(x_656);
lean_dec(x_637);
x_657 = lean_ctor_get(x_643, 1);
lean_inc(x_657);
lean_dec(x_643);
x_658 = lean_ctor_get(x_644, 0);
lean_inc(x_658);
lean_dec(x_644);
lean_inc(x_658);
x_659 = l_Lean_FVarIdSet_insert(x_57, x_658);
x_660 = l_Lean_Expr_replaceFVarId(x_58, x_658, x_657);
lean_dec(x_657);
lean_dec(x_58);
x_661 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_661, 0, x_659);
lean_ctor_set(x_661, 1, x_660);
x_12 = x_661;
x_13 = x_656;
goto block_18;
}
case 2:
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_662 = lean_ctor_get(x_637, 1);
lean_inc(x_662);
lean_dec(x_637);
x_663 = lean_ctor_get(x_641, 0);
lean_inc(x_663);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_664 = x_641;
} else {
 lean_dec_ref(x_641);
 x_664 = lean_box(0);
}
x_665 = lean_ctor_get(x_643, 1);
lean_inc(x_665);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_666 = x_643;
} else {
 lean_dec_ref(x_643);
 x_666 = lean_box(0);
}
x_667 = lean_ctor_get(x_644, 0);
lean_inc(x_667);
lean_dec(x_644);
x_668 = l_Lean_Expr_mvar___override(x_667);
if (lean_is_scalar(x_666)) {
 x_669 = lean_alloc_ctor(0, 2, 0);
} else {
 x_669 = x_666;
}
lean_ctor_set(x_669, 0, x_668);
lean_ctor_set(x_669, 1, x_665);
if (lean_is_scalar(x_664)) {
 x_670 = lean_alloc_ctor(0, 2, 0);
} else {
 x_670 = x_664;
}
lean_ctor_set(x_670, 0, x_663);
lean_ctor_set(x_670, 1, x_669);
if (lean_is_scalar(x_642)) {
 x_671 = lean_alloc_ctor(1, 1, 0);
} else {
 x_671 = x_642;
}
lean_ctor_set(x_671, 0, x_670);
x_672 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_671, x_59, x_60, x_61, x_62, x_662);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_671);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_672;
goto block_24;
}
case 3:
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_673 = lean_ctor_get(x_637, 1);
lean_inc(x_673);
lean_dec(x_637);
x_674 = lean_ctor_get(x_641, 0);
lean_inc(x_674);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_675 = x_641;
} else {
 lean_dec_ref(x_641);
 x_675 = lean_box(0);
}
x_676 = lean_ctor_get(x_643, 1);
lean_inc(x_676);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_677 = x_643;
} else {
 lean_dec_ref(x_643);
 x_677 = lean_box(0);
}
x_678 = lean_ctor_get(x_644, 0);
lean_inc(x_678);
lean_dec(x_644);
x_679 = l_Lean_Expr_sort___override(x_678);
if (lean_is_scalar(x_677)) {
 x_680 = lean_alloc_ctor(0, 2, 0);
} else {
 x_680 = x_677;
}
lean_ctor_set(x_680, 0, x_679);
lean_ctor_set(x_680, 1, x_676);
if (lean_is_scalar(x_675)) {
 x_681 = lean_alloc_ctor(0, 2, 0);
} else {
 x_681 = x_675;
}
lean_ctor_set(x_681, 0, x_674);
lean_ctor_set(x_681, 1, x_680);
if (lean_is_scalar(x_642)) {
 x_682 = lean_alloc_ctor(1, 1, 0);
} else {
 x_682 = x_642;
}
lean_ctor_set(x_682, 0, x_681);
x_683 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_682, x_59, x_60, x_61, x_62, x_673);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_682);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_683;
goto block_24;
}
case 4:
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_684 = lean_ctor_get(x_637, 1);
lean_inc(x_684);
lean_dec(x_637);
x_685 = lean_ctor_get(x_641, 0);
lean_inc(x_685);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_686 = x_641;
} else {
 lean_dec_ref(x_641);
 x_686 = lean_box(0);
}
x_687 = lean_ctor_get(x_643, 1);
lean_inc(x_687);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_688 = x_643;
} else {
 lean_dec_ref(x_643);
 x_688 = lean_box(0);
}
x_689 = lean_ctor_get(x_644, 0);
lean_inc(x_689);
x_690 = lean_ctor_get(x_644, 1);
lean_inc(x_690);
lean_dec(x_644);
x_691 = l_Lean_Expr_const___override(x_689, x_690);
if (lean_is_scalar(x_688)) {
 x_692 = lean_alloc_ctor(0, 2, 0);
} else {
 x_692 = x_688;
}
lean_ctor_set(x_692, 0, x_691);
lean_ctor_set(x_692, 1, x_687);
if (lean_is_scalar(x_686)) {
 x_693 = lean_alloc_ctor(0, 2, 0);
} else {
 x_693 = x_686;
}
lean_ctor_set(x_693, 0, x_685);
lean_ctor_set(x_693, 1, x_692);
if (lean_is_scalar(x_642)) {
 x_694 = lean_alloc_ctor(1, 1, 0);
} else {
 x_694 = x_642;
}
lean_ctor_set(x_694, 0, x_693);
x_695 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_694, x_59, x_60, x_61, x_62, x_684);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_694);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_695;
goto block_24;
}
case 5:
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_696 = lean_ctor_get(x_637, 1);
lean_inc(x_696);
lean_dec(x_637);
x_697 = lean_ctor_get(x_641, 0);
lean_inc(x_697);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_698 = x_641;
} else {
 lean_dec_ref(x_641);
 x_698 = lean_box(0);
}
x_699 = lean_ctor_get(x_643, 1);
lean_inc(x_699);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_700 = x_643;
} else {
 lean_dec_ref(x_643);
 x_700 = lean_box(0);
}
x_701 = lean_ctor_get(x_644, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_644, 1);
lean_inc(x_702);
lean_dec(x_644);
x_703 = l_Lean_Expr_app___override(x_701, x_702);
if (lean_is_scalar(x_700)) {
 x_704 = lean_alloc_ctor(0, 2, 0);
} else {
 x_704 = x_700;
}
lean_ctor_set(x_704, 0, x_703);
lean_ctor_set(x_704, 1, x_699);
if (lean_is_scalar(x_698)) {
 x_705 = lean_alloc_ctor(0, 2, 0);
} else {
 x_705 = x_698;
}
lean_ctor_set(x_705, 0, x_697);
lean_ctor_set(x_705, 1, x_704);
if (lean_is_scalar(x_642)) {
 x_706 = lean_alloc_ctor(1, 1, 0);
} else {
 x_706 = x_642;
}
lean_ctor_set(x_706, 0, x_705);
x_707 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_706, x_59, x_60, x_61, x_62, x_696);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_706);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_707;
goto block_24;
}
case 6:
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; uint8_t x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_708 = lean_ctor_get(x_637, 1);
lean_inc(x_708);
lean_dec(x_637);
x_709 = lean_ctor_get(x_641, 0);
lean_inc(x_709);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_710 = x_641;
} else {
 lean_dec_ref(x_641);
 x_710 = lean_box(0);
}
x_711 = lean_ctor_get(x_643, 1);
lean_inc(x_711);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_712 = x_643;
} else {
 lean_dec_ref(x_643);
 x_712 = lean_box(0);
}
x_713 = lean_ctor_get(x_644, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_644, 1);
lean_inc(x_714);
x_715 = lean_ctor_get(x_644, 2);
lean_inc(x_715);
x_716 = lean_ctor_get_uint8(x_644, sizeof(void*)*3 + 8);
lean_dec(x_644);
x_717 = l_Lean_Expr_lam___override(x_713, x_714, x_715, x_716);
if (lean_is_scalar(x_712)) {
 x_718 = lean_alloc_ctor(0, 2, 0);
} else {
 x_718 = x_712;
}
lean_ctor_set(x_718, 0, x_717);
lean_ctor_set(x_718, 1, x_711);
if (lean_is_scalar(x_710)) {
 x_719 = lean_alloc_ctor(0, 2, 0);
} else {
 x_719 = x_710;
}
lean_ctor_set(x_719, 0, x_709);
lean_ctor_set(x_719, 1, x_718);
if (lean_is_scalar(x_642)) {
 x_720 = lean_alloc_ctor(1, 1, 0);
} else {
 x_720 = x_642;
}
lean_ctor_set(x_720, 0, x_719);
x_721 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_720, x_59, x_60, x_61, x_62, x_708);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_720);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_721;
goto block_24;
}
case 7:
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; uint8_t x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_722 = lean_ctor_get(x_637, 1);
lean_inc(x_722);
lean_dec(x_637);
x_723 = lean_ctor_get(x_641, 0);
lean_inc(x_723);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_724 = x_641;
} else {
 lean_dec_ref(x_641);
 x_724 = lean_box(0);
}
x_725 = lean_ctor_get(x_643, 1);
lean_inc(x_725);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_726 = x_643;
} else {
 lean_dec_ref(x_643);
 x_726 = lean_box(0);
}
x_727 = lean_ctor_get(x_644, 0);
lean_inc(x_727);
x_728 = lean_ctor_get(x_644, 1);
lean_inc(x_728);
x_729 = lean_ctor_get(x_644, 2);
lean_inc(x_729);
x_730 = lean_ctor_get_uint8(x_644, sizeof(void*)*3 + 8);
lean_dec(x_644);
x_731 = l_Lean_Expr_forallE___override(x_727, x_728, x_729, x_730);
if (lean_is_scalar(x_726)) {
 x_732 = lean_alloc_ctor(0, 2, 0);
} else {
 x_732 = x_726;
}
lean_ctor_set(x_732, 0, x_731);
lean_ctor_set(x_732, 1, x_725);
if (lean_is_scalar(x_724)) {
 x_733 = lean_alloc_ctor(0, 2, 0);
} else {
 x_733 = x_724;
}
lean_ctor_set(x_733, 0, x_723);
lean_ctor_set(x_733, 1, x_732);
if (lean_is_scalar(x_642)) {
 x_734 = lean_alloc_ctor(1, 1, 0);
} else {
 x_734 = x_642;
}
lean_ctor_set(x_734, 0, x_733);
x_735 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_734, x_59, x_60, x_61, x_62, x_722);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_734);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_735;
goto block_24;
}
case 8:
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; uint8_t x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_736 = lean_ctor_get(x_637, 1);
lean_inc(x_736);
lean_dec(x_637);
x_737 = lean_ctor_get(x_641, 0);
lean_inc(x_737);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_738 = x_641;
} else {
 lean_dec_ref(x_641);
 x_738 = lean_box(0);
}
x_739 = lean_ctor_get(x_643, 1);
lean_inc(x_739);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_740 = x_643;
} else {
 lean_dec_ref(x_643);
 x_740 = lean_box(0);
}
x_741 = lean_ctor_get(x_644, 0);
lean_inc(x_741);
x_742 = lean_ctor_get(x_644, 1);
lean_inc(x_742);
x_743 = lean_ctor_get(x_644, 2);
lean_inc(x_743);
x_744 = lean_ctor_get(x_644, 3);
lean_inc(x_744);
x_745 = lean_ctor_get_uint8(x_644, sizeof(void*)*4 + 8);
lean_dec(x_644);
x_746 = l_Lean_Expr_letE___override(x_741, x_742, x_743, x_744, x_745);
if (lean_is_scalar(x_740)) {
 x_747 = lean_alloc_ctor(0, 2, 0);
} else {
 x_747 = x_740;
}
lean_ctor_set(x_747, 0, x_746);
lean_ctor_set(x_747, 1, x_739);
if (lean_is_scalar(x_738)) {
 x_748 = lean_alloc_ctor(0, 2, 0);
} else {
 x_748 = x_738;
}
lean_ctor_set(x_748, 0, x_737);
lean_ctor_set(x_748, 1, x_747);
if (lean_is_scalar(x_642)) {
 x_749 = lean_alloc_ctor(1, 1, 0);
} else {
 x_749 = x_642;
}
lean_ctor_set(x_749, 0, x_748);
x_750 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_749, x_59, x_60, x_61, x_62, x_736);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_749);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_750;
goto block_24;
}
case 9:
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_751 = lean_ctor_get(x_637, 1);
lean_inc(x_751);
lean_dec(x_637);
x_752 = lean_ctor_get(x_641, 0);
lean_inc(x_752);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_753 = x_641;
} else {
 lean_dec_ref(x_641);
 x_753 = lean_box(0);
}
x_754 = lean_ctor_get(x_643, 1);
lean_inc(x_754);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_755 = x_643;
} else {
 lean_dec_ref(x_643);
 x_755 = lean_box(0);
}
x_756 = lean_ctor_get(x_644, 0);
lean_inc(x_756);
lean_dec(x_644);
x_757 = l_Lean_Expr_lit___override(x_756);
if (lean_is_scalar(x_755)) {
 x_758 = lean_alloc_ctor(0, 2, 0);
} else {
 x_758 = x_755;
}
lean_ctor_set(x_758, 0, x_757);
lean_ctor_set(x_758, 1, x_754);
if (lean_is_scalar(x_753)) {
 x_759 = lean_alloc_ctor(0, 2, 0);
} else {
 x_759 = x_753;
}
lean_ctor_set(x_759, 0, x_752);
lean_ctor_set(x_759, 1, x_758);
if (lean_is_scalar(x_642)) {
 x_760 = lean_alloc_ctor(1, 1, 0);
} else {
 x_760 = x_642;
}
lean_ctor_set(x_760, 0, x_759);
x_761 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_760, x_59, x_60, x_61, x_62, x_751);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_760);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_761;
goto block_24;
}
case 10:
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_762 = lean_ctor_get(x_637, 1);
lean_inc(x_762);
lean_dec(x_637);
x_763 = lean_ctor_get(x_641, 0);
lean_inc(x_763);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_764 = x_641;
} else {
 lean_dec_ref(x_641);
 x_764 = lean_box(0);
}
x_765 = lean_ctor_get(x_643, 1);
lean_inc(x_765);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_766 = x_643;
} else {
 lean_dec_ref(x_643);
 x_766 = lean_box(0);
}
x_767 = lean_ctor_get(x_644, 0);
lean_inc(x_767);
x_768 = lean_ctor_get(x_644, 1);
lean_inc(x_768);
lean_dec(x_644);
x_769 = l_Lean_Expr_mdata___override(x_767, x_768);
if (lean_is_scalar(x_766)) {
 x_770 = lean_alloc_ctor(0, 2, 0);
} else {
 x_770 = x_766;
}
lean_ctor_set(x_770, 0, x_769);
lean_ctor_set(x_770, 1, x_765);
if (lean_is_scalar(x_764)) {
 x_771 = lean_alloc_ctor(0, 2, 0);
} else {
 x_771 = x_764;
}
lean_ctor_set(x_771, 0, x_763);
lean_ctor_set(x_771, 1, x_770);
if (lean_is_scalar(x_642)) {
 x_772 = lean_alloc_ctor(1, 1, 0);
} else {
 x_772 = x_642;
}
lean_ctor_set(x_772, 0, x_771);
x_773 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_772, x_59, x_60, x_61, x_62, x_762);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_772);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_773;
goto block_24;
}
default: 
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_774 = lean_ctor_get(x_637, 1);
lean_inc(x_774);
lean_dec(x_637);
x_775 = lean_ctor_get(x_641, 0);
lean_inc(x_775);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_776 = x_641;
} else {
 lean_dec_ref(x_641);
 x_776 = lean_box(0);
}
x_777 = lean_ctor_get(x_643, 1);
lean_inc(x_777);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_778 = x_643;
} else {
 lean_dec_ref(x_643);
 x_778 = lean_box(0);
}
x_779 = lean_ctor_get(x_644, 0);
lean_inc(x_779);
x_780 = lean_ctor_get(x_644, 1);
lean_inc(x_780);
x_781 = lean_ctor_get(x_644, 2);
lean_inc(x_781);
lean_dec(x_644);
x_782 = l_Lean_Expr_proj___override(x_779, x_780, x_781);
if (lean_is_scalar(x_778)) {
 x_783 = lean_alloc_ctor(0, 2, 0);
} else {
 x_783 = x_778;
}
lean_ctor_set(x_783, 0, x_782);
lean_ctor_set(x_783, 1, x_777);
if (lean_is_scalar(x_776)) {
 x_784 = lean_alloc_ctor(0, 2, 0);
} else {
 x_784 = x_776;
}
lean_ctor_set(x_784, 0, x_775);
lean_ctor_set(x_784, 1, x_783);
if (lean_is_scalar(x_642)) {
 x_785 = lean_alloc_ctor(1, 1, 0);
} else {
 x_785 = x_642;
}
lean_ctor_set(x_785, 0, x_784);
x_786 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_785, x_59, x_60, x_61, x_62, x_774);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_785);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_786;
goto block_24;
}
}
}
}
else
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_787 = lean_ctor_get(x_637, 0);
lean_inc(x_787);
x_788 = lean_ctor_get(x_637, 1);
lean_inc(x_788);
if (lean_is_exclusive(x_637)) {
 lean_ctor_release(x_637, 0);
 lean_ctor_release(x_637, 1);
 x_789 = x_637;
} else {
 lean_dec_ref(x_637);
 x_789 = lean_box(0);
}
if (lean_is_scalar(x_789)) {
 x_790 = lean_alloc_ctor(1, 2, 0);
} else {
 x_790 = x_789;
}
lean_ctor_set(x_790, 0, x_787);
lean_ctor_set(x_790, 1, x_788);
return x_790;
}
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_791 = lean_ctor_get(x_634, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_634, 1);
lean_inc(x_792);
if (lean_is_exclusive(x_634)) {
 lean_ctor_release(x_634, 0);
 lean_ctor_release(x_634, 1);
 x_793 = x_634;
} else {
 lean_dec_ref(x_634);
 x_793 = lean_box(0);
}
if (lean_is_scalar(x_793)) {
 x_794 = lean_alloc_ctor(1, 2, 0);
} else {
 x_794 = x_793;
}
lean_ctor_set(x_794, 0, x_791);
lean_ctor_set(x_794, 1, x_792);
return x_794;
}
}
}
}
}
block_18:
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_5, x_15);
x_5 = x_16;
x_6 = x_12;
x_11 = x_13;
goto _start;
}
block_24:
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_19; uint8_t x_25; 
x_25 = lean_usize_dec_lt(x_5, x_4);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_11);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_796; 
x_27 = lean_mk_string_unchecked("Elab", 4, 4);
x_28 = lean_mk_string_unchecked("definition", 10, 10);
x_29 = l_Lean_Name_mkStr2(x_27, x_28);
lean_inc(x_29);
x_30 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_29, x_7, x_8, x_9, x_10, x_11);
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
x_34 = lean_array_uget(x_3, x_5);
x_796 = lean_unbox(x_31);
lean_dec(x_31);
if (x_796 == 0)
{
lean_object* x_797; lean_object* x_798; 
lean_dec(x_29);
x_797 = lean_ctor_get(x_6, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_6, 1);
lean_inc(x_798);
lean_dec(x_6);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_57 = x_797;
x_58 = x_798;
x_59 = x_7;
x_60 = x_8;
x_61 = x_9;
x_62 = x_10;
x_63 = x_32;
goto block_795;
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; 
x_799 = lean_ctor_get(x_6, 0);
lean_inc(x_799);
x_800 = lean_ctor_get(x_6, 1);
lean_inc(x_800);
lean_dec(x_6);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_34);
x_801 = lean_infer_type(x_34, x_7, x_8, x_9, x_10, x_32);
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; 
x_802 = lean_ctor_get(x_801, 0);
lean_inc(x_802);
x_803 = lean_ctor_get(x_801, 1);
lean_inc(x_803);
lean_dec(x_801);
x_804 = lean_mk_string_unchecked(">> simpEqnType: ", 16, 16);
x_805 = l_Lean_stringToMessageData(x_804);
lean_dec(x_804);
x_806 = l_Lean_MessageData_ofExpr(x_802);
x_807 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_807, 0, x_805);
lean_ctor_set(x_807, 1, x_806);
x_808 = lean_mk_string_unchecked(", ", 2, 2);
x_809 = l_Lean_stringToMessageData(x_808);
lean_dec(x_808);
x_810 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_810, 0, x_807);
lean_ctor_set(x_810, 1, x_809);
lean_inc(x_800);
x_811 = l_Lean_MessageData_ofExpr(x_800);
x_812 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_812, 0, x_810);
lean_ctor_set(x_812, 1, x_811);
x_813 = lean_mk_string_unchecked("", 0, 0);
x_814 = l_Lean_stringToMessageData(x_813);
lean_dec(x_813);
x_815 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_815, 0, x_812);
lean_ctor_set(x_815, 1, x_814);
x_816 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_29, x_815, x_7, x_8, x_9, x_10, x_803);
x_817 = lean_ctor_get(x_816, 1);
lean_inc(x_817);
lean_dec(x_816);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_57 = x_799;
x_58 = x_800;
x_59 = x_7;
x_60 = x_8;
x_61 = x_9;
x_62 = x_10;
x_63 = x_817;
goto block_795;
}
else
{
uint8_t x_818; 
lean_dec(x_800);
lean_dec(x_799);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_818 = !lean_is_exclusive(x_801);
if (x_818 == 0)
{
return x_801;
}
else
{
lean_object* x_819; lean_object* x_820; lean_object* x_821; 
x_819 = lean_ctor_get(x_801, 0);
x_820 = lean_ctor_get(x_801, 1);
lean_inc(x_820);
lean_inc(x_819);
lean_dec(x_801);
x_821 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_821, 0, x_819);
lean_ctor_set(x_821, 1, x_820);
return x_821;
}
}
}
block_56:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_mk_empty_array_with_capacity(x_43);
x_45 = lean_array_push(x_44, x_34);
x_46 = lean_box(1);
x_47 = lean_unbox(x_46);
x_48 = l_Lean_Meta_mkForallFVars(x_45, x_37, x_36, x_25, x_47, x_38, x_39, x_40, x_41, x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_45);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
if (lean_is_scalar(x_33)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_33;
}
lean_ctor_set(x_51, 0, x_35);
lean_ctor_set(x_51, 1, x_49);
x_12 = x_51;
x_13 = x_50;
goto block_18;
}
else
{
uint8_t x_52; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
return x_48;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_48, 0);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_48);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
block_795:
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Lean_Expr_fvarId_x21(x_34);
x_65 = l_Lean_RBNode_findCore___at___Lean_Meta_removeUnused_spec__0___redArg(x_2, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_box(0);
x_67 = l_Lean_RBNode_findCore___at___Lean_Meta_removeUnused_spec__0___redArg(x_57, x_64);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_34);
x_68 = lean_infer_type(x_34, x_59, x_60, x_61, x_62, x_63);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
x_71 = l_Lean_Meta_matchEq_x3f(x_69, x_59, x_60, x_61, x_62, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; uint8_t x_74; 
lean_dec(x_64);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_unbox(x_66);
x_35 = x_57;
x_36 = x_74;
x_37 = x_58;
x_38 = x_59;
x_39 = x_60;
x_40 = x_61;
x_41 = x_62;
x_42 = x_73;
goto block_56;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
lean_dec(x_71);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_78);
x_80 = l_Lean_Meta_isExprDefEq(x_78, x_79, x_59, x_60, x_61, x_62, x_77);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
lean_dec(x_78);
lean_dec(x_64);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_unbox(x_66);
x_35 = x_57;
x_36 = x_84;
x_37 = x_58;
x_38 = x_59;
x_39 = x_60;
x_40 = x_61;
x_41 = x_62;
x_42 = x_83;
goto block_56;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
lean_dec(x_80);
lean_inc(x_64);
lean_inc(x_58);
x_86 = l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg(x_58, x_64, x_60, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
uint8_t x_89; 
lean_dec(x_78);
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_34);
lean_dec(x_33);
x_89 = !lean_is_exclusive(x_86);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_86, 1);
x_91 = lean_ctor_get(x_86, 0);
lean_dec(x_91);
lean_ctor_set(x_86, 1, x_58);
lean_ctor_set(x_86, 0, x_57);
x_12 = x_86;
x_13 = x_90;
goto block_18;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_86, 1);
lean_inc(x_92);
lean_dec(x_86);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_57);
lean_ctor_set(x_93, 1, x_58);
x_12 = x_93;
x_13 = x_92;
goto block_18;
}
}
else
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_86);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_86, 1);
x_96 = lean_ctor_get(x_86, 0);
lean_dec(x_96);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
x_97 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_lhsDependsOn(x_58, x_64, x_59, x_60, x_61, x_62, x_95);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_33);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = l_Lean_Meta_mkEqRefl(x_78, x_59, x_60, x_61, x_62, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Lean_Expr_replaceFVar(x_58, x_34, x_102);
lean_dec(x_102);
lean_dec(x_58);
lean_ctor_set(x_86, 1, x_104);
lean_ctor_set(x_86, 0, x_57);
x_12 = x_86;
x_13 = x_103;
goto block_18;
}
else
{
uint8_t x_105; 
lean_free_object(x_86);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_101);
if (x_105 == 0)
{
return x_101;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_101, 0);
x_107 = lean_ctor_get(x_101, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_101);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; uint8_t x_110; 
lean_free_object(x_86);
lean_dec(x_78);
x_109 = lean_ctor_get(x_97, 1);
lean_inc(x_109);
lean_dec(x_97);
x_110 = lean_unbox(x_66);
x_35 = x_57;
x_36 = x_110;
x_37 = x_58;
x_38 = x_59;
x_39 = x_60;
x_40 = x_61;
x_41 = x_62;
x_42 = x_109;
goto block_56;
}
}
else
{
uint8_t x_111; 
lean_free_object(x_86);
lean_dec(x_78);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_97);
if (x_111 == 0)
{
return x_97;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_97, 0);
x_113 = lean_ctor_get(x_97, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_97);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_86, 1);
lean_inc(x_115);
lean_dec(x_86);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
x_116 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_lhsDependsOn(x_58, x_64, x_59, x_60, x_61, x_62, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_unbox(x_117);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_33);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
lean_dec(x_116);
x_120 = l_Lean_Meta_mkEqRefl(x_78, x_59, x_60, x_61, x_62, x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = l_Lean_Expr_replaceFVar(x_58, x_34, x_121);
lean_dec(x_121);
lean_dec(x_58);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_57);
lean_ctor_set(x_124, 1, x_123);
x_12 = x_124;
x_13 = x_122;
goto block_18;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_125 = lean_ctor_get(x_120, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_120, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_127 = x_120;
} else {
 lean_dec_ref(x_120);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
else
{
lean_object* x_129; uint8_t x_130; 
lean_dec(x_78);
x_129 = lean_ctor_get(x_116, 1);
lean_inc(x_129);
lean_dec(x_116);
x_130 = lean_unbox(x_66);
x_35 = x_57;
x_36 = x_130;
x_37 = x_58;
x_38 = x_59;
x_39 = x_60;
x_40 = x_61;
x_41 = x_62;
x_42 = x_129;
goto block_56;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_78);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_131 = lean_ctor_get(x_116, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_116, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_133 = x_116;
} else {
 lean_dec_ref(x_116);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_78);
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_80);
if (x_135 == 0)
{
return x_80;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_80, 0);
x_137 = lean_ctor_get(x_80, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_80);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_71);
if (x_139 == 0)
{
return x_71;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_71, 0);
x_141 = lean_ctor_get(x_71, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_71);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_68);
if (x_143 == 0)
{
return x_68;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_68, 0);
x_145 = lean_ctor_get(x_68, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_68);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
lean_dec(x_67);
lean_dec(x_33);
lean_inc(x_58);
x_147 = l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg(x_58, x_64, x_60, x_63);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_unbox(x_148);
lean_dec(x_148);
if (x_149 == 0)
{
uint8_t x_150; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_34);
x_150 = !lean_is_exclusive(x_147);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_147, 1);
x_152 = lean_ctor_get(x_147, 0);
lean_dec(x_152);
lean_ctor_set(x_147, 1, x_58);
lean_ctor_set(x_147, 0, x_57);
x_12 = x_147;
x_13 = x_151;
goto block_18;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_147, 1);
lean_inc(x_153);
lean_dec(x_147);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_57);
lean_ctor_set(x_154, 1, x_58);
x_12 = x_154;
x_13 = x_153;
goto block_18;
}
}
else
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_147);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; uint8_t x_163; lean_object* x_164; 
x_156 = lean_ctor_get(x_147, 1);
x_157 = lean_ctor_get(x_147, 0);
lean_dec(x_157);
x_158 = lean_unsigned_to_nat(1u);
x_159 = lean_mk_empty_array_with_capacity(x_158);
x_160 = lean_array_push(x_159, x_34);
x_161 = lean_box(1);
x_162 = lean_unbox(x_66);
x_163 = lean_unbox(x_161);
x_164 = l_Lean_Meta_mkForallFVars(x_160, x_58, x_162, x_25, x_163, x_59, x_60, x_61, x_62, x_156);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_160);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
lean_ctor_set(x_147, 1, x_165);
lean_ctor_set(x_147, 0, x_57);
x_12 = x_147;
x_13 = x_166;
goto block_18;
}
else
{
uint8_t x_167; 
lean_free_object(x_147);
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_167 = !lean_is_exclusive(x_164);
if (x_167 == 0)
{
return x_164;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_164, 0);
x_169 = lean_ctor_get(x_164, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_164);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; uint8_t x_177; lean_object* x_178; 
x_171 = lean_ctor_get(x_147, 1);
lean_inc(x_171);
lean_dec(x_147);
x_172 = lean_unsigned_to_nat(1u);
x_173 = lean_mk_empty_array_with_capacity(x_172);
x_174 = lean_array_push(x_173, x_34);
x_175 = lean_box(1);
x_176 = lean_unbox(x_66);
x_177 = lean_unbox(x_175);
x_178 = l_Lean_Meta_mkForallFVars(x_174, x_58, x_176, x_25, x_177, x_59, x_60, x_61, x_62, x_171);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_174);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_57);
lean_ctor_set(x_181, 1, x_179);
x_12 = x_181;
x_13 = x_180;
goto block_18;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_182 = lean_ctor_get(x_178, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_178, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_184 = x_178;
} else {
 lean_dec_ref(x_178);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
}
}
}
else
{
lean_object* x_186; uint8_t x_187; 
lean_dec(x_64);
lean_dec(x_33);
x_186 = lean_ctor_get(x_65, 0);
lean_inc(x_186);
lean_dec(x_65);
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_186, 1);
lean_dec(x_188);
x_189 = lean_ctor_get(x_186, 0);
lean_dec(x_189);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
x_190 = lean_infer_type(x_34, x_59, x_60, x_61, x_62, x_63);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
x_193 = l_Lean_Meta_matchEq_x3f(x_191, x_59, x_60, x_61, x_62, x_192);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_195);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_196;
goto block_24;
}
else
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_194);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_194, 0);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
switch (lean_obj_tag(x_200)) {
case 0:
{
lean_object* x_201; uint8_t x_202; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_201 = lean_ctor_get(x_193, 1);
lean_inc(x_201);
lean_dec(x_193);
x_202 = !lean_is_exclusive(x_198);
if (x_202 == 0)
{
lean_object* x_203; uint8_t x_204; 
x_203 = lean_ctor_get(x_198, 1);
lean_dec(x_203);
x_204 = !lean_is_exclusive(x_199);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_205 = lean_ctor_get(x_199, 0);
lean_dec(x_205);
x_206 = lean_ctor_get(x_200, 0);
lean_inc(x_206);
lean_dec(x_200);
x_207 = l_Lean_Expr_bvar___override(x_206);
lean_ctor_set(x_199, 0, x_207);
x_208 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_201);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_208;
goto block_24;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_209 = lean_ctor_get(x_199, 1);
lean_inc(x_209);
lean_dec(x_199);
x_210 = lean_ctor_get(x_200, 0);
lean_inc(x_210);
lean_dec(x_200);
x_211 = l_Lean_Expr_bvar___override(x_210);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_209);
lean_ctor_set(x_198, 1, x_212);
x_213 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_201);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_213;
goto block_24;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_214 = lean_ctor_get(x_198, 0);
lean_inc(x_214);
lean_dec(x_198);
x_215 = lean_ctor_get(x_199, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_216 = x_199;
} else {
 lean_dec_ref(x_199);
 x_216 = lean_box(0);
}
x_217 = lean_ctor_get(x_200, 0);
lean_inc(x_217);
lean_dec(x_200);
x_218 = l_Lean_Expr_bvar___override(x_217);
if (lean_is_scalar(x_216)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_216;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_215);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_214);
lean_ctor_set(x_220, 1, x_219);
lean_ctor_set(x_194, 0, x_220);
x_221 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_201);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_221;
goto block_24;
}
}
case 1:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_free_object(x_194);
lean_dec(x_198);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
x_222 = lean_ctor_get(x_193, 1);
lean_inc(x_222);
lean_dec(x_193);
x_223 = lean_ctor_get(x_199, 1);
lean_inc(x_223);
lean_dec(x_199);
x_224 = lean_ctor_get(x_200, 0);
lean_inc(x_224);
lean_dec(x_200);
lean_inc(x_224);
x_225 = l_Lean_FVarIdSet_insert(x_57, x_224);
x_226 = l_Lean_Expr_replaceFVarId(x_58, x_224, x_223);
lean_dec(x_223);
lean_dec(x_58);
lean_ctor_set(x_186, 1, x_226);
lean_ctor_set(x_186, 0, x_225);
x_12 = x_186;
x_13 = x_222;
goto block_18;
}
case 2:
{
lean_object* x_227; uint8_t x_228; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_227 = lean_ctor_get(x_193, 1);
lean_inc(x_227);
lean_dec(x_193);
x_228 = !lean_is_exclusive(x_198);
if (x_228 == 0)
{
lean_object* x_229; uint8_t x_230; 
x_229 = lean_ctor_get(x_198, 1);
lean_dec(x_229);
x_230 = !lean_is_exclusive(x_199);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_231 = lean_ctor_get(x_199, 0);
lean_dec(x_231);
x_232 = lean_ctor_get(x_200, 0);
lean_inc(x_232);
lean_dec(x_200);
x_233 = l_Lean_Expr_mvar___override(x_232);
lean_ctor_set(x_199, 0, x_233);
x_234 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_227);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_234;
goto block_24;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_235 = lean_ctor_get(x_199, 1);
lean_inc(x_235);
lean_dec(x_199);
x_236 = lean_ctor_get(x_200, 0);
lean_inc(x_236);
lean_dec(x_200);
x_237 = l_Lean_Expr_mvar___override(x_236);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_235);
lean_ctor_set(x_198, 1, x_238);
x_239 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_227);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_239;
goto block_24;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_240 = lean_ctor_get(x_198, 0);
lean_inc(x_240);
lean_dec(x_198);
x_241 = lean_ctor_get(x_199, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_242 = x_199;
} else {
 lean_dec_ref(x_199);
 x_242 = lean_box(0);
}
x_243 = lean_ctor_get(x_200, 0);
lean_inc(x_243);
lean_dec(x_200);
x_244 = l_Lean_Expr_mvar___override(x_243);
if (lean_is_scalar(x_242)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_242;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_241);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_240);
lean_ctor_set(x_246, 1, x_245);
lean_ctor_set(x_194, 0, x_246);
x_247 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_227);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_247;
goto block_24;
}
}
case 3:
{
lean_object* x_248; uint8_t x_249; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_248 = lean_ctor_get(x_193, 1);
lean_inc(x_248);
lean_dec(x_193);
x_249 = !lean_is_exclusive(x_198);
if (x_249 == 0)
{
lean_object* x_250; uint8_t x_251; 
x_250 = lean_ctor_get(x_198, 1);
lean_dec(x_250);
x_251 = !lean_is_exclusive(x_199);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_ctor_get(x_199, 0);
lean_dec(x_252);
x_253 = lean_ctor_get(x_200, 0);
lean_inc(x_253);
lean_dec(x_200);
x_254 = l_Lean_Expr_sort___override(x_253);
lean_ctor_set(x_199, 0, x_254);
x_255 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_248);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_255;
goto block_24;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_256 = lean_ctor_get(x_199, 1);
lean_inc(x_256);
lean_dec(x_199);
x_257 = lean_ctor_get(x_200, 0);
lean_inc(x_257);
lean_dec(x_200);
x_258 = l_Lean_Expr_sort___override(x_257);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_256);
lean_ctor_set(x_198, 1, x_259);
x_260 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_248);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_260;
goto block_24;
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_261 = lean_ctor_get(x_198, 0);
lean_inc(x_261);
lean_dec(x_198);
x_262 = lean_ctor_get(x_199, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_263 = x_199;
} else {
 lean_dec_ref(x_199);
 x_263 = lean_box(0);
}
x_264 = lean_ctor_get(x_200, 0);
lean_inc(x_264);
lean_dec(x_200);
x_265 = l_Lean_Expr_sort___override(x_264);
if (lean_is_scalar(x_263)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_263;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_262);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_261);
lean_ctor_set(x_267, 1, x_266);
lean_ctor_set(x_194, 0, x_267);
x_268 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_248);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_268;
goto block_24;
}
}
case 4:
{
lean_object* x_269; uint8_t x_270; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_269 = lean_ctor_get(x_193, 1);
lean_inc(x_269);
lean_dec(x_193);
x_270 = !lean_is_exclusive(x_198);
if (x_270 == 0)
{
lean_object* x_271; uint8_t x_272; 
x_271 = lean_ctor_get(x_198, 1);
lean_dec(x_271);
x_272 = !lean_is_exclusive(x_199);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_273 = lean_ctor_get(x_199, 0);
lean_dec(x_273);
x_274 = lean_ctor_get(x_200, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_200, 1);
lean_inc(x_275);
lean_dec(x_200);
x_276 = l_Lean_Expr_const___override(x_274, x_275);
lean_ctor_set(x_199, 0, x_276);
x_277 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_269);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_277;
goto block_24;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_278 = lean_ctor_get(x_199, 1);
lean_inc(x_278);
lean_dec(x_199);
x_279 = lean_ctor_get(x_200, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_200, 1);
lean_inc(x_280);
lean_dec(x_200);
x_281 = l_Lean_Expr_const___override(x_279, x_280);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_278);
lean_ctor_set(x_198, 1, x_282);
x_283 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_269);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_283;
goto block_24;
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_284 = lean_ctor_get(x_198, 0);
lean_inc(x_284);
lean_dec(x_198);
x_285 = lean_ctor_get(x_199, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_286 = x_199;
} else {
 lean_dec_ref(x_199);
 x_286 = lean_box(0);
}
x_287 = lean_ctor_get(x_200, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_200, 1);
lean_inc(x_288);
lean_dec(x_200);
x_289 = l_Lean_Expr_const___override(x_287, x_288);
if (lean_is_scalar(x_286)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_286;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_285);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_284);
lean_ctor_set(x_291, 1, x_290);
lean_ctor_set(x_194, 0, x_291);
x_292 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_269);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_292;
goto block_24;
}
}
case 5:
{
lean_object* x_293; uint8_t x_294; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_293 = lean_ctor_get(x_193, 1);
lean_inc(x_293);
lean_dec(x_193);
x_294 = !lean_is_exclusive(x_198);
if (x_294 == 0)
{
lean_object* x_295; uint8_t x_296; 
x_295 = lean_ctor_get(x_198, 1);
lean_dec(x_295);
x_296 = !lean_is_exclusive(x_199);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_297 = lean_ctor_get(x_199, 0);
lean_dec(x_297);
x_298 = lean_ctor_get(x_200, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_200, 1);
lean_inc(x_299);
lean_dec(x_200);
x_300 = l_Lean_Expr_app___override(x_298, x_299);
lean_ctor_set(x_199, 0, x_300);
x_301 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_293);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_301;
goto block_24;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_302 = lean_ctor_get(x_199, 1);
lean_inc(x_302);
lean_dec(x_199);
x_303 = lean_ctor_get(x_200, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_200, 1);
lean_inc(x_304);
lean_dec(x_200);
x_305 = l_Lean_Expr_app___override(x_303, x_304);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_302);
lean_ctor_set(x_198, 1, x_306);
x_307 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_293);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_307;
goto block_24;
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_308 = lean_ctor_get(x_198, 0);
lean_inc(x_308);
lean_dec(x_198);
x_309 = lean_ctor_get(x_199, 1);
lean_inc(x_309);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_310 = x_199;
} else {
 lean_dec_ref(x_199);
 x_310 = lean_box(0);
}
x_311 = lean_ctor_get(x_200, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_200, 1);
lean_inc(x_312);
lean_dec(x_200);
x_313 = l_Lean_Expr_app___override(x_311, x_312);
if (lean_is_scalar(x_310)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_310;
}
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_309);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_308);
lean_ctor_set(x_315, 1, x_314);
lean_ctor_set(x_194, 0, x_315);
x_316 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_293);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_316;
goto block_24;
}
}
case 6:
{
lean_object* x_317; uint8_t x_318; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_317 = lean_ctor_get(x_193, 1);
lean_inc(x_317);
lean_dec(x_193);
x_318 = !lean_is_exclusive(x_198);
if (x_318 == 0)
{
lean_object* x_319; uint8_t x_320; 
x_319 = lean_ctor_get(x_198, 1);
lean_dec(x_319);
x_320 = !lean_is_exclusive(x_199);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; lean_object* x_326; lean_object* x_327; 
x_321 = lean_ctor_get(x_199, 0);
lean_dec(x_321);
x_322 = lean_ctor_get(x_200, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_200, 1);
lean_inc(x_323);
x_324 = lean_ctor_get(x_200, 2);
lean_inc(x_324);
x_325 = lean_ctor_get_uint8(x_200, sizeof(void*)*3 + 8);
lean_dec(x_200);
x_326 = l_Lean_Expr_lam___override(x_322, x_323, x_324, x_325);
lean_ctor_set(x_199, 0, x_326);
x_327 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_317);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_327;
goto block_24;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_328 = lean_ctor_get(x_199, 1);
lean_inc(x_328);
lean_dec(x_199);
x_329 = lean_ctor_get(x_200, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_200, 1);
lean_inc(x_330);
x_331 = lean_ctor_get(x_200, 2);
lean_inc(x_331);
x_332 = lean_ctor_get_uint8(x_200, sizeof(void*)*3 + 8);
lean_dec(x_200);
x_333 = l_Lean_Expr_lam___override(x_329, x_330, x_331, x_332);
x_334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_328);
lean_ctor_set(x_198, 1, x_334);
x_335 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_317);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_335;
goto block_24;
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_336 = lean_ctor_get(x_198, 0);
lean_inc(x_336);
lean_dec(x_198);
x_337 = lean_ctor_get(x_199, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_338 = x_199;
} else {
 lean_dec_ref(x_199);
 x_338 = lean_box(0);
}
x_339 = lean_ctor_get(x_200, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_200, 1);
lean_inc(x_340);
x_341 = lean_ctor_get(x_200, 2);
lean_inc(x_341);
x_342 = lean_ctor_get_uint8(x_200, sizeof(void*)*3 + 8);
lean_dec(x_200);
x_343 = l_Lean_Expr_lam___override(x_339, x_340, x_341, x_342);
if (lean_is_scalar(x_338)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_338;
}
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_337);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_336);
lean_ctor_set(x_345, 1, x_344);
lean_ctor_set(x_194, 0, x_345);
x_346 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_317);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_346;
goto block_24;
}
}
case 7:
{
lean_object* x_347; uint8_t x_348; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_347 = lean_ctor_get(x_193, 1);
lean_inc(x_347);
lean_dec(x_193);
x_348 = !lean_is_exclusive(x_198);
if (x_348 == 0)
{
lean_object* x_349; uint8_t x_350; 
x_349 = lean_ctor_get(x_198, 1);
lean_dec(x_349);
x_350 = !lean_is_exclusive(x_199);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; lean_object* x_357; 
x_351 = lean_ctor_get(x_199, 0);
lean_dec(x_351);
x_352 = lean_ctor_get(x_200, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_200, 1);
lean_inc(x_353);
x_354 = lean_ctor_get(x_200, 2);
lean_inc(x_354);
x_355 = lean_ctor_get_uint8(x_200, sizeof(void*)*3 + 8);
lean_dec(x_200);
x_356 = l_Lean_Expr_forallE___override(x_352, x_353, x_354, x_355);
lean_ctor_set(x_199, 0, x_356);
x_357 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_347);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_357;
goto block_24;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_358 = lean_ctor_get(x_199, 1);
lean_inc(x_358);
lean_dec(x_199);
x_359 = lean_ctor_get(x_200, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_200, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_200, 2);
lean_inc(x_361);
x_362 = lean_ctor_get_uint8(x_200, sizeof(void*)*3 + 8);
lean_dec(x_200);
x_363 = l_Lean_Expr_forallE___override(x_359, x_360, x_361, x_362);
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_358);
lean_ctor_set(x_198, 1, x_364);
x_365 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_347);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_365;
goto block_24;
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_366 = lean_ctor_get(x_198, 0);
lean_inc(x_366);
lean_dec(x_198);
x_367 = lean_ctor_get(x_199, 1);
lean_inc(x_367);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_368 = x_199;
} else {
 lean_dec_ref(x_199);
 x_368 = lean_box(0);
}
x_369 = lean_ctor_get(x_200, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_200, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_200, 2);
lean_inc(x_371);
x_372 = lean_ctor_get_uint8(x_200, sizeof(void*)*3 + 8);
lean_dec(x_200);
x_373 = l_Lean_Expr_forallE___override(x_369, x_370, x_371, x_372);
if (lean_is_scalar(x_368)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_368;
}
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_367);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_366);
lean_ctor_set(x_375, 1, x_374);
lean_ctor_set(x_194, 0, x_375);
x_376 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_347);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_376;
goto block_24;
}
}
case 8:
{
lean_object* x_377; uint8_t x_378; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_377 = lean_ctor_get(x_193, 1);
lean_inc(x_377);
lean_dec(x_193);
x_378 = !lean_is_exclusive(x_198);
if (x_378 == 0)
{
lean_object* x_379; uint8_t x_380; 
x_379 = lean_ctor_get(x_198, 1);
lean_dec(x_379);
x_380 = !lean_is_exclusive(x_199);
if (x_380 == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; uint8_t x_386; lean_object* x_387; lean_object* x_388; 
x_381 = lean_ctor_get(x_199, 0);
lean_dec(x_381);
x_382 = lean_ctor_get(x_200, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_200, 1);
lean_inc(x_383);
x_384 = lean_ctor_get(x_200, 2);
lean_inc(x_384);
x_385 = lean_ctor_get(x_200, 3);
lean_inc(x_385);
x_386 = lean_ctor_get_uint8(x_200, sizeof(void*)*4 + 8);
lean_dec(x_200);
x_387 = l_Lean_Expr_letE___override(x_382, x_383, x_384, x_385, x_386);
lean_ctor_set(x_199, 0, x_387);
x_388 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_377);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_388;
goto block_24;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_389 = lean_ctor_get(x_199, 1);
lean_inc(x_389);
lean_dec(x_199);
x_390 = lean_ctor_get(x_200, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_200, 1);
lean_inc(x_391);
x_392 = lean_ctor_get(x_200, 2);
lean_inc(x_392);
x_393 = lean_ctor_get(x_200, 3);
lean_inc(x_393);
x_394 = lean_ctor_get_uint8(x_200, sizeof(void*)*4 + 8);
lean_dec(x_200);
x_395 = l_Lean_Expr_letE___override(x_390, x_391, x_392, x_393, x_394);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_389);
lean_ctor_set(x_198, 1, x_396);
x_397 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_377);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_397;
goto block_24;
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_398 = lean_ctor_get(x_198, 0);
lean_inc(x_398);
lean_dec(x_198);
x_399 = lean_ctor_get(x_199, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_400 = x_199;
} else {
 lean_dec_ref(x_199);
 x_400 = lean_box(0);
}
x_401 = lean_ctor_get(x_200, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_200, 1);
lean_inc(x_402);
x_403 = lean_ctor_get(x_200, 2);
lean_inc(x_403);
x_404 = lean_ctor_get(x_200, 3);
lean_inc(x_404);
x_405 = lean_ctor_get_uint8(x_200, sizeof(void*)*4 + 8);
lean_dec(x_200);
x_406 = l_Lean_Expr_letE___override(x_401, x_402, x_403, x_404, x_405);
if (lean_is_scalar(x_400)) {
 x_407 = lean_alloc_ctor(0, 2, 0);
} else {
 x_407 = x_400;
}
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_399);
x_408 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_408, 0, x_398);
lean_ctor_set(x_408, 1, x_407);
lean_ctor_set(x_194, 0, x_408);
x_409 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_377);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_409;
goto block_24;
}
}
case 9:
{
lean_object* x_410; uint8_t x_411; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_410 = lean_ctor_get(x_193, 1);
lean_inc(x_410);
lean_dec(x_193);
x_411 = !lean_is_exclusive(x_198);
if (x_411 == 0)
{
lean_object* x_412; uint8_t x_413; 
x_412 = lean_ctor_get(x_198, 1);
lean_dec(x_412);
x_413 = !lean_is_exclusive(x_199);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_414 = lean_ctor_get(x_199, 0);
lean_dec(x_414);
x_415 = lean_ctor_get(x_200, 0);
lean_inc(x_415);
lean_dec(x_200);
x_416 = l_Lean_Expr_lit___override(x_415);
lean_ctor_set(x_199, 0, x_416);
x_417 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_410);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_417;
goto block_24;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_418 = lean_ctor_get(x_199, 1);
lean_inc(x_418);
lean_dec(x_199);
x_419 = lean_ctor_get(x_200, 0);
lean_inc(x_419);
lean_dec(x_200);
x_420 = l_Lean_Expr_lit___override(x_419);
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_418);
lean_ctor_set(x_198, 1, x_421);
x_422 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_410);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_422;
goto block_24;
}
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_423 = lean_ctor_get(x_198, 0);
lean_inc(x_423);
lean_dec(x_198);
x_424 = lean_ctor_get(x_199, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_425 = x_199;
} else {
 lean_dec_ref(x_199);
 x_425 = lean_box(0);
}
x_426 = lean_ctor_get(x_200, 0);
lean_inc(x_426);
lean_dec(x_200);
x_427 = l_Lean_Expr_lit___override(x_426);
if (lean_is_scalar(x_425)) {
 x_428 = lean_alloc_ctor(0, 2, 0);
} else {
 x_428 = x_425;
}
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_424);
x_429 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_429, 0, x_423);
lean_ctor_set(x_429, 1, x_428);
lean_ctor_set(x_194, 0, x_429);
x_430 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_410);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_430;
goto block_24;
}
}
case 10:
{
lean_object* x_431; uint8_t x_432; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_431 = lean_ctor_get(x_193, 1);
lean_inc(x_431);
lean_dec(x_193);
x_432 = !lean_is_exclusive(x_198);
if (x_432 == 0)
{
lean_object* x_433; uint8_t x_434; 
x_433 = lean_ctor_get(x_198, 1);
lean_dec(x_433);
x_434 = !lean_is_exclusive(x_199);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_435 = lean_ctor_get(x_199, 0);
lean_dec(x_435);
x_436 = lean_ctor_get(x_200, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_200, 1);
lean_inc(x_437);
lean_dec(x_200);
x_438 = l_Lean_Expr_mdata___override(x_436, x_437);
lean_ctor_set(x_199, 0, x_438);
x_439 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_431);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_439;
goto block_24;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_440 = lean_ctor_get(x_199, 1);
lean_inc(x_440);
lean_dec(x_199);
x_441 = lean_ctor_get(x_200, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_200, 1);
lean_inc(x_442);
lean_dec(x_200);
x_443 = l_Lean_Expr_mdata___override(x_441, x_442);
x_444 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_440);
lean_ctor_set(x_198, 1, x_444);
x_445 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_431);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_445;
goto block_24;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_446 = lean_ctor_get(x_198, 0);
lean_inc(x_446);
lean_dec(x_198);
x_447 = lean_ctor_get(x_199, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_448 = x_199;
} else {
 lean_dec_ref(x_199);
 x_448 = lean_box(0);
}
x_449 = lean_ctor_get(x_200, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_200, 1);
lean_inc(x_450);
lean_dec(x_200);
x_451 = l_Lean_Expr_mdata___override(x_449, x_450);
if (lean_is_scalar(x_448)) {
 x_452 = lean_alloc_ctor(0, 2, 0);
} else {
 x_452 = x_448;
}
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_447);
x_453 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_453, 0, x_446);
lean_ctor_set(x_453, 1, x_452);
lean_ctor_set(x_194, 0, x_453);
x_454 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_431);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_454;
goto block_24;
}
}
default: 
{
lean_object* x_455; uint8_t x_456; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_455 = lean_ctor_get(x_193, 1);
lean_inc(x_455);
lean_dec(x_193);
x_456 = !lean_is_exclusive(x_198);
if (x_456 == 0)
{
lean_object* x_457; uint8_t x_458; 
x_457 = lean_ctor_get(x_198, 1);
lean_dec(x_457);
x_458 = !lean_is_exclusive(x_199);
if (x_458 == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_459 = lean_ctor_get(x_199, 0);
lean_dec(x_459);
x_460 = lean_ctor_get(x_200, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_200, 1);
lean_inc(x_461);
x_462 = lean_ctor_get(x_200, 2);
lean_inc(x_462);
lean_dec(x_200);
x_463 = l_Lean_Expr_proj___override(x_460, x_461, x_462);
lean_ctor_set(x_199, 0, x_463);
x_464 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_455);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_464;
goto block_24;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_465 = lean_ctor_get(x_199, 1);
lean_inc(x_465);
lean_dec(x_199);
x_466 = lean_ctor_get(x_200, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_200, 1);
lean_inc(x_467);
x_468 = lean_ctor_get(x_200, 2);
lean_inc(x_468);
lean_dec(x_200);
x_469 = l_Lean_Expr_proj___override(x_466, x_467, x_468);
x_470 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_470, 0, x_469);
lean_ctor_set(x_470, 1, x_465);
lean_ctor_set(x_198, 1, x_470);
x_471 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_455);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_471;
goto block_24;
}
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_472 = lean_ctor_get(x_198, 0);
lean_inc(x_472);
lean_dec(x_198);
x_473 = lean_ctor_get(x_199, 1);
lean_inc(x_473);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_474 = x_199;
} else {
 lean_dec_ref(x_199);
 x_474 = lean_box(0);
}
x_475 = lean_ctor_get(x_200, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_200, 1);
lean_inc(x_476);
x_477 = lean_ctor_get(x_200, 2);
lean_inc(x_477);
lean_dec(x_200);
x_478 = l_Lean_Expr_proj___override(x_475, x_476, x_477);
if (lean_is_scalar(x_474)) {
 x_479 = lean_alloc_ctor(0, 2, 0);
} else {
 x_479 = x_474;
}
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_473);
x_480 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_480, 0, x_472);
lean_ctor_set(x_480, 1, x_479);
lean_ctor_set(x_194, 0, x_480);
x_481 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_194, x_59, x_60, x_61, x_62, x_455);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_194);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_481;
goto block_24;
}
}
}
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_194, 0);
lean_inc(x_482);
lean_dec(x_194);
x_483 = lean_ctor_get(x_482, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_483, 0);
lean_inc(x_484);
switch (lean_obj_tag(x_484)) {
case 0:
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_485 = lean_ctor_get(x_193, 1);
lean_inc(x_485);
lean_dec(x_193);
x_486 = lean_ctor_get(x_482, 0);
lean_inc(x_486);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_487 = x_482;
} else {
 lean_dec_ref(x_482);
 x_487 = lean_box(0);
}
x_488 = lean_ctor_get(x_483, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_489 = x_483;
} else {
 lean_dec_ref(x_483);
 x_489 = lean_box(0);
}
x_490 = lean_ctor_get(x_484, 0);
lean_inc(x_490);
lean_dec(x_484);
x_491 = l_Lean_Expr_bvar___override(x_490);
if (lean_is_scalar(x_489)) {
 x_492 = lean_alloc_ctor(0, 2, 0);
} else {
 x_492 = x_489;
}
lean_ctor_set(x_492, 0, x_491);
lean_ctor_set(x_492, 1, x_488);
if (lean_is_scalar(x_487)) {
 x_493 = lean_alloc_ctor(0, 2, 0);
} else {
 x_493 = x_487;
}
lean_ctor_set(x_493, 0, x_486);
lean_ctor_set(x_493, 1, x_492);
x_494 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_494, 0, x_493);
x_495 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_494, x_59, x_60, x_61, x_62, x_485);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_494);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_495;
goto block_24;
}
case 1:
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_482);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
x_496 = lean_ctor_get(x_193, 1);
lean_inc(x_496);
lean_dec(x_193);
x_497 = lean_ctor_get(x_483, 1);
lean_inc(x_497);
lean_dec(x_483);
x_498 = lean_ctor_get(x_484, 0);
lean_inc(x_498);
lean_dec(x_484);
lean_inc(x_498);
x_499 = l_Lean_FVarIdSet_insert(x_57, x_498);
x_500 = l_Lean_Expr_replaceFVarId(x_58, x_498, x_497);
lean_dec(x_497);
lean_dec(x_58);
lean_ctor_set(x_186, 1, x_500);
lean_ctor_set(x_186, 0, x_499);
x_12 = x_186;
x_13 = x_496;
goto block_18;
}
case 2:
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_501 = lean_ctor_get(x_193, 1);
lean_inc(x_501);
lean_dec(x_193);
x_502 = lean_ctor_get(x_482, 0);
lean_inc(x_502);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_503 = x_482;
} else {
 lean_dec_ref(x_482);
 x_503 = lean_box(0);
}
x_504 = lean_ctor_get(x_483, 1);
lean_inc(x_504);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_505 = x_483;
} else {
 lean_dec_ref(x_483);
 x_505 = lean_box(0);
}
x_506 = lean_ctor_get(x_484, 0);
lean_inc(x_506);
lean_dec(x_484);
x_507 = l_Lean_Expr_mvar___override(x_506);
if (lean_is_scalar(x_505)) {
 x_508 = lean_alloc_ctor(0, 2, 0);
} else {
 x_508 = x_505;
}
lean_ctor_set(x_508, 0, x_507);
lean_ctor_set(x_508, 1, x_504);
if (lean_is_scalar(x_503)) {
 x_509 = lean_alloc_ctor(0, 2, 0);
} else {
 x_509 = x_503;
}
lean_ctor_set(x_509, 0, x_502);
lean_ctor_set(x_509, 1, x_508);
x_510 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_510, 0, x_509);
x_511 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_510, x_59, x_60, x_61, x_62, x_501);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_510);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_511;
goto block_24;
}
case 3:
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_512 = lean_ctor_get(x_193, 1);
lean_inc(x_512);
lean_dec(x_193);
x_513 = lean_ctor_get(x_482, 0);
lean_inc(x_513);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_514 = x_482;
} else {
 lean_dec_ref(x_482);
 x_514 = lean_box(0);
}
x_515 = lean_ctor_get(x_483, 1);
lean_inc(x_515);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_516 = x_483;
} else {
 lean_dec_ref(x_483);
 x_516 = lean_box(0);
}
x_517 = lean_ctor_get(x_484, 0);
lean_inc(x_517);
lean_dec(x_484);
x_518 = l_Lean_Expr_sort___override(x_517);
if (lean_is_scalar(x_516)) {
 x_519 = lean_alloc_ctor(0, 2, 0);
} else {
 x_519 = x_516;
}
lean_ctor_set(x_519, 0, x_518);
lean_ctor_set(x_519, 1, x_515);
if (lean_is_scalar(x_514)) {
 x_520 = lean_alloc_ctor(0, 2, 0);
} else {
 x_520 = x_514;
}
lean_ctor_set(x_520, 0, x_513);
lean_ctor_set(x_520, 1, x_519);
x_521 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_521, 0, x_520);
x_522 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_521, x_59, x_60, x_61, x_62, x_512);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_521);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_522;
goto block_24;
}
case 4:
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_523 = lean_ctor_get(x_193, 1);
lean_inc(x_523);
lean_dec(x_193);
x_524 = lean_ctor_get(x_482, 0);
lean_inc(x_524);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_525 = x_482;
} else {
 lean_dec_ref(x_482);
 x_525 = lean_box(0);
}
x_526 = lean_ctor_get(x_483, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_527 = x_483;
} else {
 lean_dec_ref(x_483);
 x_527 = lean_box(0);
}
x_528 = lean_ctor_get(x_484, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_484, 1);
lean_inc(x_529);
lean_dec(x_484);
x_530 = l_Lean_Expr_const___override(x_528, x_529);
if (lean_is_scalar(x_527)) {
 x_531 = lean_alloc_ctor(0, 2, 0);
} else {
 x_531 = x_527;
}
lean_ctor_set(x_531, 0, x_530);
lean_ctor_set(x_531, 1, x_526);
if (lean_is_scalar(x_525)) {
 x_532 = lean_alloc_ctor(0, 2, 0);
} else {
 x_532 = x_525;
}
lean_ctor_set(x_532, 0, x_524);
lean_ctor_set(x_532, 1, x_531);
x_533 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_533, 0, x_532);
x_534 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_533, x_59, x_60, x_61, x_62, x_523);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_533);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_534;
goto block_24;
}
case 5:
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_535 = lean_ctor_get(x_193, 1);
lean_inc(x_535);
lean_dec(x_193);
x_536 = lean_ctor_get(x_482, 0);
lean_inc(x_536);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_537 = x_482;
} else {
 lean_dec_ref(x_482);
 x_537 = lean_box(0);
}
x_538 = lean_ctor_get(x_483, 1);
lean_inc(x_538);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_539 = x_483;
} else {
 lean_dec_ref(x_483);
 x_539 = lean_box(0);
}
x_540 = lean_ctor_get(x_484, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_484, 1);
lean_inc(x_541);
lean_dec(x_484);
x_542 = l_Lean_Expr_app___override(x_540, x_541);
if (lean_is_scalar(x_539)) {
 x_543 = lean_alloc_ctor(0, 2, 0);
} else {
 x_543 = x_539;
}
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_538);
if (lean_is_scalar(x_537)) {
 x_544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_544 = x_537;
}
lean_ctor_set(x_544, 0, x_536);
lean_ctor_set(x_544, 1, x_543);
x_545 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_545, 0, x_544);
x_546 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_545, x_59, x_60, x_61, x_62, x_535);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_545);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_546;
goto block_24;
}
case 6:
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; uint8_t x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_547 = lean_ctor_get(x_193, 1);
lean_inc(x_547);
lean_dec(x_193);
x_548 = lean_ctor_get(x_482, 0);
lean_inc(x_548);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_549 = x_482;
} else {
 lean_dec_ref(x_482);
 x_549 = lean_box(0);
}
x_550 = lean_ctor_get(x_483, 1);
lean_inc(x_550);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_551 = x_483;
} else {
 lean_dec_ref(x_483);
 x_551 = lean_box(0);
}
x_552 = lean_ctor_get(x_484, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_484, 1);
lean_inc(x_553);
x_554 = lean_ctor_get(x_484, 2);
lean_inc(x_554);
x_555 = lean_ctor_get_uint8(x_484, sizeof(void*)*3 + 8);
lean_dec(x_484);
x_556 = l_Lean_Expr_lam___override(x_552, x_553, x_554, x_555);
if (lean_is_scalar(x_551)) {
 x_557 = lean_alloc_ctor(0, 2, 0);
} else {
 x_557 = x_551;
}
lean_ctor_set(x_557, 0, x_556);
lean_ctor_set(x_557, 1, x_550);
if (lean_is_scalar(x_549)) {
 x_558 = lean_alloc_ctor(0, 2, 0);
} else {
 x_558 = x_549;
}
lean_ctor_set(x_558, 0, x_548);
lean_ctor_set(x_558, 1, x_557);
x_559 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_559, 0, x_558);
x_560 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_559, x_59, x_60, x_61, x_62, x_547);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_559);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_560;
goto block_24;
}
case 7:
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; uint8_t x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_561 = lean_ctor_get(x_193, 1);
lean_inc(x_561);
lean_dec(x_193);
x_562 = lean_ctor_get(x_482, 0);
lean_inc(x_562);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_563 = x_482;
} else {
 lean_dec_ref(x_482);
 x_563 = lean_box(0);
}
x_564 = lean_ctor_get(x_483, 1);
lean_inc(x_564);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_565 = x_483;
} else {
 lean_dec_ref(x_483);
 x_565 = lean_box(0);
}
x_566 = lean_ctor_get(x_484, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_484, 1);
lean_inc(x_567);
x_568 = lean_ctor_get(x_484, 2);
lean_inc(x_568);
x_569 = lean_ctor_get_uint8(x_484, sizeof(void*)*3 + 8);
lean_dec(x_484);
x_570 = l_Lean_Expr_forallE___override(x_566, x_567, x_568, x_569);
if (lean_is_scalar(x_565)) {
 x_571 = lean_alloc_ctor(0, 2, 0);
} else {
 x_571 = x_565;
}
lean_ctor_set(x_571, 0, x_570);
lean_ctor_set(x_571, 1, x_564);
if (lean_is_scalar(x_563)) {
 x_572 = lean_alloc_ctor(0, 2, 0);
} else {
 x_572 = x_563;
}
lean_ctor_set(x_572, 0, x_562);
lean_ctor_set(x_572, 1, x_571);
x_573 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_573, 0, x_572);
x_574 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_573, x_59, x_60, x_61, x_62, x_561);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_573);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_574;
goto block_24;
}
case 8:
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; uint8_t x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_575 = lean_ctor_get(x_193, 1);
lean_inc(x_575);
lean_dec(x_193);
x_576 = lean_ctor_get(x_482, 0);
lean_inc(x_576);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_577 = x_482;
} else {
 lean_dec_ref(x_482);
 x_577 = lean_box(0);
}
x_578 = lean_ctor_get(x_483, 1);
lean_inc(x_578);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_579 = x_483;
} else {
 lean_dec_ref(x_483);
 x_579 = lean_box(0);
}
x_580 = lean_ctor_get(x_484, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_484, 1);
lean_inc(x_581);
x_582 = lean_ctor_get(x_484, 2);
lean_inc(x_582);
x_583 = lean_ctor_get(x_484, 3);
lean_inc(x_583);
x_584 = lean_ctor_get_uint8(x_484, sizeof(void*)*4 + 8);
lean_dec(x_484);
x_585 = l_Lean_Expr_letE___override(x_580, x_581, x_582, x_583, x_584);
if (lean_is_scalar(x_579)) {
 x_586 = lean_alloc_ctor(0, 2, 0);
} else {
 x_586 = x_579;
}
lean_ctor_set(x_586, 0, x_585);
lean_ctor_set(x_586, 1, x_578);
if (lean_is_scalar(x_577)) {
 x_587 = lean_alloc_ctor(0, 2, 0);
} else {
 x_587 = x_577;
}
lean_ctor_set(x_587, 0, x_576);
lean_ctor_set(x_587, 1, x_586);
x_588 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_588, 0, x_587);
x_589 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_588, x_59, x_60, x_61, x_62, x_575);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_588);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_589;
goto block_24;
}
case 9:
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_590 = lean_ctor_get(x_193, 1);
lean_inc(x_590);
lean_dec(x_193);
x_591 = lean_ctor_get(x_482, 0);
lean_inc(x_591);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_592 = x_482;
} else {
 lean_dec_ref(x_482);
 x_592 = lean_box(0);
}
x_593 = lean_ctor_get(x_483, 1);
lean_inc(x_593);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_594 = x_483;
} else {
 lean_dec_ref(x_483);
 x_594 = lean_box(0);
}
x_595 = lean_ctor_get(x_484, 0);
lean_inc(x_595);
lean_dec(x_484);
x_596 = l_Lean_Expr_lit___override(x_595);
if (lean_is_scalar(x_594)) {
 x_597 = lean_alloc_ctor(0, 2, 0);
} else {
 x_597 = x_594;
}
lean_ctor_set(x_597, 0, x_596);
lean_ctor_set(x_597, 1, x_593);
if (lean_is_scalar(x_592)) {
 x_598 = lean_alloc_ctor(0, 2, 0);
} else {
 x_598 = x_592;
}
lean_ctor_set(x_598, 0, x_591);
lean_ctor_set(x_598, 1, x_597);
x_599 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_599, 0, x_598);
x_600 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_599, x_59, x_60, x_61, x_62, x_590);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_599);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_600;
goto block_24;
}
case 10:
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_601 = lean_ctor_get(x_193, 1);
lean_inc(x_601);
lean_dec(x_193);
x_602 = lean_ctor_get(x_482, 0);
lean_inc(x_602);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_603 = x_482;
} else {
 lean_dec_ref(x_482);
 x_603 = lean_box(0);
}
x_604 = lean_ctor_get(x_483, 1);
lean_inc(x_604);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_605 = x_483;
} else {
 lean_dec_ref(x_483);
 x_605 = lean_box(0);
}
x_606 = lean_ctor_get(x_484, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_484, 1);
lean_inc(x_607);
lean_dec(x_484);
x_608 = l_Lean_Expr_mdata___override(x_606, x_607);
if (lean_is_scalar(x_605)) {
 x_609 = lean_alloc_ctor(0, 2, 0);
} else {
 x_609 = x_605;
}
lean_ctor_set(x_609, 0, x_608);
lean_ctor_set(x_609, 1, x_604);
if (lean_is_scalar(x_603)) {
 x_610 = lean_alloc_ctor(0, 2, 0);
} else {
 x_610 = x_603;
}
lean_ctor_set(x_610, 0, x_602);
lean_ctor_set(x_610, 1, x_609);
x_611 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_611, 0, x_610);
x_612 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_611, x_59, x_60, x_61, x_62, x_601);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_611);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_612;
goto block_24;
}
default: 
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_free_object(x_186);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_613 = lean_ctor_get(x_193, 1);
lean_inc(x_613);
lean_dec(x_193);
x_614 = lean_ctor_get(x_482, 0);
lean_inc(x_614);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_615 = x_482;
} else {
 lean_dec_ref(x_482);
 x_615 = lean_box(0);
}
x_616 = lean_ctor_get(x_483, 1);
lean_inc(x_616);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_617 = x_483;
} else {
 lean_dec_ref(x_483);
 x_617 = lean_box(0);
}
x_618 = lean_ctor_get(x_484, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_484, 1);
lean_inc(x_619);
x_620 = lean_ctor_get(x_484, 2);
lean_inc(x_620);
lean_dec(x_484);
x_621 = l_Lean_Expr_proj___override(x_618, x_619, x_620);
if (lean_is_scalar(x_617)) {
 x_622 = lean_alloc_ctor(0, 2, 0);
} else {
 x_622 = x_617;
}
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_616);
if (lean_is_scalar(x_615)) {
 x_623 = lean_alloc_ctor(0, 2, 0);
} else {
 x_623 = x_615;
}
lean_ctor_set(x_623, 0, x_614);
lean_ctor_set(x_623, 1, x_622);
x_624 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_624, 0, x_623);
x_625 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_624, x_59, x_60, x_61, x_62, x_613);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_624);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_625;
goto block_24;
}
}
}
}
}
else
{
uint8_t x_626; 
lean_free_object(x_186);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_626 = !lean_is_exclusive(x_193);
if (x_626 == 0)
{
return x_193;
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; 
x_627 = lean_ctor_get(x_193, 0);
x_628 = lean_ctor_get(x_193, 1);
lean_inc(x_628);
lean_inc(x_627);
lean_dec(x_193);
x_629 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_629, 0, x_627);
lean_ctor_set(x_629, 1, x_628);
return x_629;
}
}
}
else
{
uint8_t x_630; 
lean_free_object(x_186);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_630 = !lean_is_exclusive(x_190);
if (x_630 == 0)
{
return x_190;
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_631 = lean_ctor_get(x_190, 0);
x_632 = lean_ctor_get(x_190, 1);
lean_inc(x_632);
lean_inc(x_631);
lean_dec(x_190);
x_633 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_633, 0, x_631);
lean_ctor_set(x_633, 1, x_632);
return x_633;
}
}
}
else
{
lean_object* x_634; 
lean_dec(x_186);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
x_634 = lean_infer_type(x_34, x_59, x_60, x_61, x_62, x_63);
if (lean_obj_tag(x_634) == 0)
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_635 = lean_ctor_get(x_634, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_634, 1);
lean_inc(x_636);
lean_dec(x_634);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
x_637 = l_Lean_Meta_matchEq_x3f(x_635, x_59, x_60, x_61, x_62, x_636);
if (lean_obj_tag(x_637) == 0)
{
lean_object* x_638; 
x_638 = lean_ctor_get(x_637, 0);
lean_inc(x_638);
if (lean_obj_tag(x_638) == 0)
{
lean_object* x_639; lean_object* x_640; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_639 = lean_ctor_get(x_637, 1);
lean_inc(x_639);
lean_dec(x_637);
x_640 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_638, x_59, x_60, x_61, x_62, x_639);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_640;
goto block_24;
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_641 = lean_ctor_get(x_638, 0);
lean_inc(x_641);
if (lean_is_exclusive(x_638)) {
 lean_ctor_release(x_638, 0);
 x_642 = x_638;
} else {
 lean_dec_ref(x_638);
 x_642 = lean_box(0);
}
x_643 = lean_ctor_get(x_641, 1);
lean_inc(x_643);
x_644 = lean_ctor_get(x_643, 0);
lean_inc(x_644);
switch (lean_obj_tag(x_644)) {
case 0:
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_645 = lean_ctor_get(x_637, 1);
lean_inc(x_645);
lean_dec(x_637);
x_646 = lean_ctor_get(x_641, 0);
lean_inc(x_646);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_647 = x_641;
} else {
 lean_dec_ref(x_641);
 x_647 = lean_box(0);
}
x_648 = lean_ctor_get(x_643, 1);
lean_inc(x_648);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_649 = x_643;
} else {
 lean_dec_ref(x_643);
 x_649 = lean_box(0);
}
x_650 = lean_ctor_get(x_644, 0);
lean_inc(x_650);
lean_dec(x_644);
x_651 = l_Lean_Expr_bvar___override(x_650);
if (lean_is_scalar(x_649)) {
 x_652 = lean_alloc_ctor(0, 2, 0);
} else {
 x_652 = x_649;
}
lean_ctor_set(x_652, 0, x_651);
lean_ctor_set(x_652, 1, x_648);
if (lean_is_scalar(x_647)) {
 x_653 = lean_alloc_ctor(0, 2, 0);
} else {
 x_653 = x_647;
}
lean_ctor_set(x_653, 0, x_646);
lean_ctor_set(x_653, 1, x_652);
if (lean_is_scalar(x_642)) {
 x_654 = lean_alloc_ctor(1, 1, 0);
} else {
 x_654 = x_642;
}
lean_ctor_set(x_654, 0, x_653);
x_655 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_654, x_59, x_60, x_61, x_62, x_645);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_654);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_655;
goto block_24;
}
case 1:
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_642);
lean_dec(x_641);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
x_656 = lean_ctor_get(x_637, 1);
lean_inc(x_656);
lean_dec(x_637);
x_657 = lean_ctor_get(x_643, 1);
lean_inc(x_657);
lean_dec(x_643);
x_658 = lean_ctor_get(x_644, 0);
lean_inc(x_658);
lean_dec(x_644);
lean_inc(x_658);
x_659 = l_Lean_FVarIdSet_insert(x_57, x_658);
x_660 = l_Lean_Expr_replaceFVarId(x_58, x_658, x_657);
lean_dec(x_657);
lean_dec(x_58);
x_661 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_661, 0, x_659);
lean_ctor_set(x_661, 1, x_660);
x_12 = x_661;
x_13 = x_656;
goto block_18;
}
case 2:
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_662 = lean_ctor_get(x_637, 1);
lean_inc(x_662);
lean_dec(x_637);
x_663 = lean_ctor_get(x_641, 0);
lean_inc(x_663);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_664 = x_641;
} else {
 lean_dec_ref(x_641);
 x_664 = lean_box(0);
}
x_665 = lean_ctor_get(x_643, 1);
lean_inc(x_665);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_666 = x_643;
} else {
 lean_dec_ref(x_643);
 x_666 = lean_box(0);
}
x_667 = lean_ctor_get(x_644, 0);
lean_inc(x_667);
lean_dec(x_644);
x_668 = l_Lean_Expr_mvar___override(x_667);
if (lean_is_scalar(x_666)) {
 x_669 = lean_alloc_ctor(0, 2, 0);
} else {
 x_669 = x_666;
}
lean_ctor_set(x_669, 0, x_668);
lean_ctor_set(x_669, 1, x_665);
if (lean_is_scalar(x_664)) {
 x_670 = lean_alloc_ctor(0, 2, 0);
} else {
 x_670 = x_664;
}
lean_ctor_set(x_670, 0, x_663);
lean_ctor_set(x_670, 1, x_669);
if (lean_is_scalar(x_642)) {
 x_671 = lean_alloc_ctor(1, 1, 0);
} else {
 x_671 = x_642;
}
lean_ctor_set(x_671, 0, x_670);
x_672 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_671, x_59, x_60, x_61, x_62, x_662);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_671);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_672;
goto block_24;
}
case 3:
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_673 = lean_ctor_get(x_637, 1);
lean_inc(x_673);
lean_dec(x_637);
x_674 = lean_ctor_get(x_641, 0);
lean_inc(x_674);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_675 = x_641;
} else {
 lean_dec_ref(x_641);
 x_675 = lean_box(0);
}
x_676 = lean_ctor_get(x_643, 1);
lean_inc(x_676);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_677 = x_643;
} else {
 lean_dec_ref(x_643);
 x_677 = lean_box(0);
}
x_678 = lean_ctor_get(x_644, 0);
lean_inc(x_678);
lean_dec(x_644);
x_679 = l_Lean_Expr_sort___override(x_678);
if (lean_is_scalar(x_677)) {
 x_680 = lean_alloc_ctor(0, 2, 0);
} else {
 x_680 = x_677;
}
lean_ctor_set(x_680, 0, x_679);
lean_ctor_set(x_680, 1, x_676);
if (lean_is_scalar(x_675)) {
 x_681 = lean_alloc_ctor(0, 2, 0);
} else {
 x_681 = x_675;
}
lean_ctor_set(x_681, 0, x_674);
lean_ctor_set(x_681, 1, x_680);
if (lean_is_scalar(x_642)) {
 x_682 = lean_alloc_ctor(1, 1, 0);
} else {
 x_682 = x_642;
}
lean_ctor_set(x_682, 0, x_681);
x_683 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_682, x_59, x_60, x_61, x_62, x_673);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_682);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_683;
goto block_24;
}
case 4:
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_684 = lean_ctor_get(x_637, 1);
lean_inc(x_684);
lean_dec(x_637);
x_685 = lean_ctor_get(x_641, 0);
lean_inc(x_685);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_686 = x_641;
} else {
 lean_dec_ref(x_641);
 x_686 = lean_box(0);
}
x_687 = lean_ctor_get(x_643, 1);
lean_inc(x_687);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_688 = x_643;
} else {
 lean_dec_ref(x_643);
 x_688 = lean_box(0);
}
x_689 = lean_ctor_get(x_644, 0);
lean_inc(x_689);
x_690 = lean_ctor_get(x_644, 1);
lean_inc(x_690);
lean_dec(x_644);
x_691 = l_Lean_Expr_const___override(x_689, x_690);
if (lean_is_scalar(x_688)) {
 x_692 = lean_alloc_ctor(0, 2, 0);
} else {
 x_692 = x_688;
}
lean_ctor_set(x_692, 0, x_691);
lean_ctor_set(x_692, 1, x_687);
if (lean_is_scalar(x_686)) {
 x_693 = lean_alloc_ctor(0, 2, 0);
} else {
 x_693 = x_686;
}
lean_ctor_set(x_693, 0, x_685);
lean_ctor_set(x_693, 1, x_692);
if (lean_is_scalar(x_642)) {
 x_694 = lean_alloc_ctor(1, 1, 0);
} else {
 x_694 = x_642;
}
lean_ctor_set(x_694, 0, x_693);
x_695 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_694, x_59, x_60, x_61, x_62, x_684);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_694);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_695;
goto block_24;
}
case 5:
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_696 = lean_ctor_get(x_637, 1);
lean_inc(x_696);
lean_dec(x_637);
x_697 = lean_ctor_get(x_641, 0);
lean_inc(x_697);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_698 = x_641;
} else {
 lean_dec_ref(x_641);
 x_698 = lean_box(0);
}
x_699 = lean_ctor_get(x_643, 1);
lean_inc(x_699);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_700 = x_643;
} else {
 lean_dec_ref(x_643);
 x_700 = lean_box(0);
}
x_701 = lean_ctor_get(x_644, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_644, 1);
lean_inc(x_702);
lean_dec(x_644);
x_703 = l_Lean_Expr_app___override(x_701, x_702);
if (lean_is_scalar(x_700)) {
 x_704 = lean_alloc_ctor(0, 2, 0);
} else {
 x_704 = x_700;
}
lean_ctor_set(x_704, 0, x_703);
lean_ctor_set(x_704, 1, x_699);
if (lean_is_scalar(x_698)) {
 x_705 = lean_alloc_ctor(0, 2, 0);
} else {
 x_705 = x_698;
}
lean_ctor_set(x_705, 0, x_697);
lean_ctor_set(x_705, 1, x_704);
if (lean_is_scalar(x_642)) {
 x_706 = lean_alloc_ctor(1, 1, 0);
} else {
 x_706 = x_642;
}
lean_ctor_set(x_706, 0, x_705);
x_707 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_706, x_59, x_60, x_61, x_62, x_696);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_706);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_707;
goto block_24;
}
case 6:
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; uint8_t x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_708 = lean_ctor_get(x_637, 1);
lean_inc(x_708);
lean_dec(x_637);
x_709 = lean_ctor_get(x_641, 0);
lean_inc(x_709);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_710 = x_641;
} else {
 lean_dec_ref(x_641);
 x_710 = lean_box(0);
}
x_711 = lean_ctor_get(x_643, 1);
lean_inc(x_711);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_712 = x_643;
} else {
 lean_dec_ref(x_643);
 x_712 = lean_box(0);
}
x_713 = lean_ctor_get(x_644, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_644, 1);
lean_inc(x_714);
x_715 = lean_ctor_get(x_644, 2);
lean_inc(x_715);
x_716 = lean_ctor_get_uint8(x_644, sizeof(void*)*3 + 8);
lean_dec(x_644);
x_717 = l_Lean_Expr_lam___override(x_713, x_714, x_715, x_716);
if (lean_is_scalar(x_712)) {
 x_718 = lean_alloc_ctor(0, 2, 0);
} else {
 x_718 = x_712;
}
lean_ctor_set(x_718, 0, x_717);
lean_ctor_set(x_718, 1, x_711);
if (lean_is_scalar(x_710)) {
 x_719 = lean_alloc_ctor(0, 2, 0);
} else {
 x_719 = x_710;
}
lean_ctor_set(x_719, 0, x_709);
lean_ctor_set(x_719, 1, x_718);
if (lean_is_scalar(x_642)) {
 x_720 = lean_alloc_ctor(1, 1, 0);
} else {
 x_720 = x_642;
}
lean_ctor_set(x_720, 0, x_719);
x_721 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_720, x_59, x_60, x_61, x_62, x_708);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_720);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_721;
goto block_24;
}
case 7:
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; uint8_t x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_722 = lean_ctor_get(x_637, 1);
lean_inc(x_722);
lean_dec(x_637);
x_723 = lean_ctor_get(x_641, 0);
lean_inc(x_723);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_724 = x_641;
} else {
 lean_dec_ref(x_641);
 x_724 = lean_box(0);
}
x_725 = lean_ctor_get(x_643, 1);
lean_inc(x_725);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_726 = x_643;
} else {
 lean_dec_ref(x_643);
 x_726 = lean_box(0);
}
x_727 = lean_ctor_get(x_644, 0);
lean_inc(x_727);
x_728 = lean_ctor_get(x_644, 1);
lean_inc(x_728);
x_729 = lean_ctor_get(x_644, 2);
lean_inc(x_729);
x_730 = lean_ctor_get_uint8(x_644, sizeof(void*)*3 + 8);
lean_dec(x_644);
x_731 = l_Lean_Expr_forallE___override(x_727, x_728, x_729, x_730);
if (lean_is_scalar(x_726)) {
 x_732 = lean_alloc_ctor(0, 2, 0);
} else {
 x_732 = x_726;
}
lean_ctor_set(x_732, 0, x_731);
lean_ctor_set(x_732, 1, x_725);
if (lean_is_scalar(x_724)) {
 x_733 = lean_alloc_ctor(0, 2, 0);
} else {
 x_733 = x_724;
}
lean_ctor_set(x_733, 0, x_723);
lean_ctor_set(x_733, 1, x_732);
if (lean_is_scalar(x_642)) {
 x_734 = lean_alloc_ctor(1, 1, 0);
} else {
 x_734 = x_642;
}
lean_ctor_set(x_734, 0, x_733);
x_735 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_734, x_59, x_60, x_61, x_62, x_722);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_734);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_735;
goto block_24;
}
case 8:
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; uint8_t x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_736 = lean_ctor_get(x_637, 1);
lean_inc(x_736);
lean_dec(x_637);
x_737 = lean_ctor_get(x_641, 0);
lean_inc(x_737);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_738 = x_641;
} else {
 lean_dec_ref(x_641);
 x_738 = lean_box(0);
}
x_739 = lean_ctor_get(x_643, 1);
lean_inc(x_739);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_740 = x_643;
} else {
 lean_dec_ref(x_643);
 x_740 = lean_box(0);
}
x_741 = lean_ctor_get(x_644, 0);
lean_inc(x_741);
x_742 = lean_ctor_get(x_644, 1);
lean_inc(x_742);
x_743 = lean_ctor_get(x_644, 2);
lean_inc(x_743);
x_744 = lean_ctor_get(x_644, 3);
lean_inc(x_744);
x_745 = lean_ctor_get_uint8(x_644, sizeof(void*)*4 + 8);
lean_dec(x_644);
x_746 = l_Lean_Expr_letE___override(x_741, x_742, x_743, x_744, x_745);
if (lean_is_scalar(x_740)) {
 x_747 = lean_alloc_ctor(0, 2, 0);
} else {
 x_747 = x_740;
}
lean_ctor_set(x_747, 0, x_746);
lean_ctor_set(x_747, 1, x_739);
if (lean_is_scalar(x_738)) {
 x_748 = lean_alloc_ctor(0, 2, 0);
} else {
 x_748 = x_738;
}
lean_ctor_set(x_748, 0, x_737);
lean_ctor_set(x_748, 1, x_747);
if (lean_is_scalar(x_642)) {
 x_749 = lean_alloc_ctor(1, 1, 0);
} else {
 x_749 = x_642;
}
lean_ctor_set(x_749, 0, x_748);
x_750 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_749, x_59, x_60, x_61, x_62, x_736);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_749);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_750;
goto block_24;
}
case 9:
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_751 = lean_ctor_get(x_637, 1);
lean_inc(x_751);
lean_dec(x_637);
x_752 = lean_ctor_get(x_641, 0);
lean_inc(x_752);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_753 = x_641;
} else {
 lean_dec_ref(x_641);
 x_753 = lean_box(0);
}
x_754 = lean_ctor_get(x_643, 1);
lean_inc(x_754);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_755 = x_643;
} else {
 lean_dec_ref(x_643);
 x_755 = lean_box(0);
}
x_756 = lean_ctor_get(x_644, 0);
lean_inc(x_756);
lean_dec(x_644);
x_757 = l_Lean_Expr_lit___override(x_756);
if (lean_is_scalar(x_755)) {
 x_758 = lean_alloc_ctor(0, 2, 0);
} else {
 x_758 = x_755;
}
lean_ctor_set(x_758, 0, x_757);
lean_ctor_set(x_758, 1, x_754);
if (lean_is_scalar(x_753)) {
 x_759 = lean_alloc_ctor(0, 2, 0);
} else {
 x_759 = x_753;
}
lean_ctor_set(x_759, 0, x_752);
lean_ctor_set(x_759, 1, x_758);
if (lean_is_scalar(x_642)) {
 x_760 = lean_alloc_ctor(1, 1, 0);
} else {
 x_760 = x_642;
}
lean_ctor_set(x_760, 0, x_759);
x_761 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_760, x_59, x_60, x_61, x_62, x_751);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_760);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_761;
goto block_24;
}
case 10:
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_762 = lean_ctor_get(x_637, 1);
lean_inc(x_762);
lean_dec(x_637);
x_763 = lean_ctor_get(x_641, 0);
lean_inc(x_763);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_764 = x_641;
} else {
 lean_dec_ref(x_641);
 x_764 = lean_box(0);
}
x_765 = lean_ctor_get(x_643, 1);
lean_inc(x_765);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_766 = x_643;
} else {
 lean_dec_ref(x_643);
 x_766 = lean_box(0);
}
x_767 = lean_ctor_get(x_644, 0);
lean_inc(x_767);
x_768 = lean_ctor_get(x_644, 1);
lean_inc(x_768);
lean_dec(x_644);
x_769 = l_Lean_Expr_mdata___override(x_767, x_768);
if (lean_is_scalar(x_766)) {
 x_770 = lean_alloc_ctor(0, 2, 0);
} else {
 x_770 = x_766;
}
lean_ctor_set(x_770, 0, x_769);
lean_ctor_set(x_770, 1, x_765);
if (lean_is_scalar(x_764)) {
 x_771 = lean_alloc_ctor(0, 2, 0);
} else {
 x_771 = x_764;
}
lean_ctor_set(x_771, 0, x_763);
lean_ctor_set(x_771, 1, x_770);
if (lean_is_scalar(x_642)) {
 x_772 = lean_alloc_ctor(1, 1, 0);
} else {
 x_772 = x_642;
}
lean_ctor_set(x_772, 0, x_771);
x_773 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_772, x_59, x_60, x_61, x_62, x_762);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_772);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_773;
goto block_24;
}
default: 
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_774 = lean_ctor_get(x_637, 1);
lean_inc(x_774);
lean_dec(x_637);
x_775 = lean_ctor_get(x_641, 0);
lean_inc(x_775);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_776 = x_641;
} else {
 lean_dec_ref(x_641);
 x_776 = lean_box(0);
}
x_777 = lean_ctor_get(x_643, 1);
lean_inc(x_777);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_778 = x_643;
} else {
 lean_dec_ref(x_643);
 x_778 = lean_box(0);
}
x_779 = lean_ctor_get(x_644, 0);
lean_inc(x_779);
x_780 = lean_ctor_get(x_644, 1);
lean_inc(x_780);
x_781 = lean_ctor_get(x_644, 2);
lean_inc(x_781);
lean_dec(x_644);
x_782 = l_Lean_Expr_proj___override(x_779, x_780, x_781);
if (lean_is_scalar(x_778)) {
 x_783 = lean_alloc_ctor(0, 2, 0);
} else {
 x_783 = x_778;
}
lean_ctor_set(x_783, 0, x_782);
lean_ctor_set(x_783, 1, x_777);
if (lean_is_scalar(x_776)) {
 x_784 = lean_alloc_ctor(0, 2, 0);
} else {
 x_784 = x_776;
}
lean_ctor_set(x_784, 0, x_775);
lean_ctor_set(x_784, 1, x_783);
if (lean_is_scalar(x_642)) {
 x_785 = lean_alloc_ctor(1, 1, 0);
} else {
 x_785 = x_642;
}
lean_ctor_set(x_785, 0, x_784);
x_786 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_57, x_58, x_785, x_59, x_60, x_61, x_62, x_774);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_785);
lean_dec(x_58);
lean_dec(x_57);
x_19 = x_786;
goto block_24;
}
}
}
}
else
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_787 = lean_ctor_get(x_637, 0);
lean_inc(x_787);
x_788 = lean_ctor_get(x_637, 1);
lean_inc(x_788);
if (lean_is_exclusive(x_637)) {
 lean_ctor_release(x_637, 0);
 lean_ctor_release(x_637, 1);
 x_789 = x_637;
} else {
 lean_dec_ref(x_637);
 x_789 = lean_box(0);
}
if (lean_is_scalar(x_789)) {
 x_790 = lean_alloc_ctor(1, 2, 0);
} else {
 x_790 = x_789;
}
lean_ctor_set(x_790, 0, x_787);
lean_ctor_set(x_790, 1, x_788);
return x_790;
}
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_791 = lean_ctor_get(x_634, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_634, 1);
lean_inc(x_792);
if (lean_is_exclusive(x_634)) {
 lean_ctor_release(x_634, 0);
 lean_ctor_release(x_634, 1);
 x_793 = x_634;
} else {
 lean_dec_ref(x_634);
 x_793 = lean_box(0);
}
if (lean_is_scalar(x_793)) {
 x_794 = lean_alloc_ctor(1, 2, 0);
} else {
 x_794 = x_793;
}
lean_ctor_set(x_794, 0, x_791);
lean_ctor_set(x_794, 1, x_792);
return x_794;
}
}
}
}
}
block_18:
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_5, x_15);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0(x_1, x_2, x_3, x_4, x_16, x_12, x_7, x_8, x_9, x_10, x_13);
return x_17;
}
block_24:
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpEqnType___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_mk_string_unchecked("Elab", 4, 4);
x_10 = lean_mk_string_unchecked("definition", 10, 10);
x_11 = l_Lean_Name_mkStr2(x_9, x_10);
lean_inc(x_11);
x_12 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_11, x_4, x_5, x_6, x_7, x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_62; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_3);
x_16 = l_Lean_Elab_Eqns_simpEqnType_collect(x_3);
x_62 = lean_unbox(x_14);
lean_dec(x_14);
if (x_62 == 0)
{
lean_free_object(x_12);
lean_dec(x_11);
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_15;
goto block_61;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_mk_string_unchecked("simpEqnType type: ", 18, 18);
x_64 = l_Lean_stringToMessageData(x_63);
lean_dec(x_63);
lean_inc(x_3);
x_65 = l_Lean_MessageData_ofExpr(x_3);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_65);
lean_ctor_set(x_12, 0, x_64);
x_66 = lean_mk_string_unchecked("", 0, 0);
x_67 = l_Lean_stringToMessageData(x_66);
lean_dec(x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_12);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_11, x_68, x_4, x_5, x_6, x_7, x_15);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_70;
goto block_61;
}
block_61:
{
lean_object* x_22; 
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_22 = l_Lean_Meta_Match_unfoldNamedPattern(x_3, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; size_t x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_box(0);
x_27 = l_Array_reverse(lean_box(0), x_2);
lean_ctor_set(x_22, 1, x_24);
lean_ctor_set(x_22, 0, x_26);
x_28 = lean_array_size(x_27);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_usize_of_nat(x_29);
x_31 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0(x_1, x_16, x_27, x_28, x_30, x_22, x_17, x_18, x_19, x_20, x_25);
lean_dec(x_27);
lean_dec(x_16);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
return x_31;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_31);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; lean_object* x_49; size_t x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_22, 0);
x_44 = lean_ctor_get(x_22, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_22);
x_45 = lean_box(0);
x_46 = l_Array_reverse(lean_box(0), x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_43);
x_48 = lean_array_size(x_46);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_usize_of_nat(x_49);
x_51 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0(x_1, x_16, x_46, x_48, x_50, x_47, x_17, x_18, x_19, x_20, x_44);
lean_dec(x_46);
lean_dec(x_16);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
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
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_59 = x_51;
} else {
 lean_dec_ref(x_51);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
return x_22;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_100; 
x_71 = lean_ctor_get(x_12, 0);
x_72 = lean_ctor_get(x_12, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_12);
lean_inc(x_3);
x_73 = l_Lean_Elab_Eqns_simpEqnType_collect(x_3);
x_100 = lean_unbox(x_71);
lean_dec(x_71);
if (x_100 == 0)
{
lean_dec(x_11);
x_74 = x_4;
x_75 = x_5;
x_76 = x_6;
x_77 = x_7;
x_78 = x_72;
goto block_99;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_101 = lean_mk_string_unchecked("simpEqnType type: ", 18, 18);
x_102 = l_Lean_stringToMessageData(x_101);
lean_dec(x_101);
lean_inc(x_3);
x_103 = l_Lean_MessageData_ofExpr(x_3);
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_mk_string_unchecked("", 0, 0);
x_106 = l_Lean_stringToMessageData(x_105);
lean_dec(x_105);
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_11, x_107, x_4, x_5, x_6, x_7, x_72);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_74 = x_4;
x_75 = x_5;
x_76 = x_6;
x_77 = x_7;
x_78 = x_109;
goto block_99;
}
block_99:
{
lean_object* x_79; 
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
x_79 = l_Lean_Meta_Match_unfoldNamedPattern(x_3, x_74, x_75, x_76, x_77, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; size_t x_86; lean_object* x_87; size_t x_88; lean_object* x_89; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = lean_box(0);
x_84 = l_Array_reverse(lean_box(0), x_2);
if (lean_is_scalar(x_82)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_82;
}
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_80);
x_86 = lean_array_size(x_84);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_usize_of_nat(x_87);
x_89 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0(x_1, x_73, x_84, x_86, x_88, x_85, x_74, x_75, x_76, x_77, x_81);
lean_dec(x_84);
lean_dec(x_73);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_89, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_97 = x_89;
} else {
 lean_dec_ref(x_89);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_2);
lean_dec(x_1);
return x_79;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpEqnType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
lean_inc(x_1);
x_7 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1, x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_simpEqnType___lam__0), 8, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_8, x_10, x_12, x_2, x_3, x_4, x_5, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0_spec__0(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_simpEqnType_spec__0(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isFVar(x_2);
if (x_3 == 0)
{
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Expr_fvarId_x21(x_2);
x_5 = l_Lean_RBNode_findCore___at___Lean_Meta_removeUnused_spec__0___redArg(x_1, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_dec(x_5);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_find_expr(x_4, x_2);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_5);
x_8 = lean_mk_string_unchecked("Eq", 2, 2);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Expr_isAppOfArity(x_2, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_33; uint8_t x_37; 
x_14 = l_Lean_Expr_appFn_x21(x_2);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_16 = l_Lean_Expr_appArg_x21(x_2);
x_37 = l_Lean_Expr_isFVar(x_15);
if (x_37 == 0)
{
lean_dec(x_15);
x_33 = x_37;
goto block_36;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lean_Expr_fvarId_x21(x_15);
lean_dec(x_15);
x_39 = l_Lean_RBNode_findCore___at___Lean_Meta_removeUnused_spec__0___redArg(x_1, x_38);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
x_33 = x_37;
goto block_36;
}
else
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_39);
x_40 = lean_box(0);
x_41 = lean_unbox(x_40);
x_17 = x_41;
goto block_32;
}
}
block_32:
{
uint8_t x_18; 
x_18 = l_Lean_Expr_isFVar(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_1);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Expr_fvarId_x21(x_16);
lean_dec(x_16);
x_22 = l_Lean_RBNode_findCore___at___Lean_Meta_removeUnused_spec__0___redArg(x_1, x_21);
lean_dec(x_21);
lean_dec(x_1);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_box(x_17);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_25);
x_30 = lean_box(x_17);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
return x_31;
}
}
}
}
block_36:
{
if (x_33 == 0)
{
x_17 = x_33;
goto block_32;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_16);
lean_dec(x_1);
x_34 = lean_box(x_11);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_pushDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_18; lean_object* x_29; 
x_29 = lean_ctor_get(x_3, 3);
lean_inc(x_29);
x_18 = x_29;
goto block_28;
block_17:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_12);
x_13 = l_Lean_FVarIdSet_insert(x_11, x_12);
x_14 = lean_array_push(x_9, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
block_28:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_18, x_5, x_8);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps(x_1, x_2, x_20, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
lean_dec(x_3);
x_9 = x_26;
x_10 = x_24;
x_11 = x_25;
x_12 = x_27;
goto block_17;
}
else
{
lean_dec(x_3);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBTree_toArray___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_RBNode_fold___at___Lean_RBTree_toArray___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps_spec__0_spec__0(x_1, x_3);
x_7 = lean_array_push(x_6, x_4);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = l_Lean_RBNode_fold___at___Lean_RBTree_toArray___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps_spec__0_spec__0(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_array_uget(x_1, x_3);
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_dec(x_4);
x_22 = l_Lean_RBNode_findCore___at___Lean_Meta_removeUnused_spec__0___redArg(x_20, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_inc(x_5);
x_23 = l_Lean_FVarId_getDecl___redArg(x_19, x_5, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_5);
x_26 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_pushDecl(x_20, x_21, x_24, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
x_10 = x_27;
x_11 = x_28;
goto block_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_27);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_10 = x_32;
x_11 = x_28;
goto block_16;
}
}
else
{
uint8_t x_33; 
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
return x_26;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_26);
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
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_5);
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
return x_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_23, 0);
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_23);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; uint8_t x_42; 
lean_dec(x_19);
x_41 = lean_ctor_get(x_22, 0);
lean_inc(x_41);
lean_dec(x_22);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
lean_ctor_set(x_41, 1, x_21);
lean_ctor_set(x_41, 0, x_20);
x_10 = x_41;
x_11 = x_9;
goto block_16;
}
else
{
lean_object* x_45; 
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_20);
lean_ctor_set(x_45, 1, x_21);
x_10 = x_45;
x_11 = x_9;
goto block_16;
}
}
}
block_16:
{
lean_object* x_12; size_t x_13; size_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_4 = x_10;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_9 = lean_unsigned_to_nat(8u);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_shiftl(x_9, x_11);
x_13 = lean_unsigned_to_nat(3u);
x_14 = lean_nat_div(x_12, x_13);
lean_dec(x_12);
x_15 = l_Nat_nextPowerOfTwo(x_14);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_mk_array(x_15, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_box(0);
x_20 = lean_mk_empty_array_with_capacity(x_10);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = l_Lean_CollectFVars_main(x_3, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_RBTree_toArray___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps_spec__0(x_23);
lean_inc(x_4);
x_25 = l_Lean_Meta_sortFVarIds___redArg(x_24, x_4, x_8);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_ctor_set(x_25, 1, x_2);
lean_ctor_set(x_25, 0, x_1);
x_29 = lean_array_size(x_27);
x_30 = lean_usize_of_nat(x_10);
x_31 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps_spec__2(x_27, x_29, x_30, x_25, x_4, x_5, x_6, x_7, x_28);
lean_dec(x_27);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_31, 0, x_37);
return x_31;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_31, 0);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_31);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_42 = x_38;
} else {
 lean_dec_ref(x_38);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_31);
if (x_45 == 0)
{
return x_31;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_31, 0);
x_47 = lean_ctor_get(x_31, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_31);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_25, 0);
x_50 = lean_ctor_get(x_25, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_25);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_2);
x_52 = lean_array_size(x_49);
x_53 = lean_usize_of_nat(x_10);
x_54 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps_spec__2(x_49, x_52, x_53, x_51, x_4, x_5, x_6, x_7, x_50);
lean_dec(x_49);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_60 = x_55;
} else {
 lean_dec_ref(x_55);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
if (lean_is_scalar(x_57)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_57;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_56);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_54, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_54, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_65 = x_54;
} else {
 lean_dec_ref(x_54);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_pushDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_pushDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps_spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_6 = lean_st_ref_get(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_instantiateMVarsCore(x_9, x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_take(x_2, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 4);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20, x_15);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_11);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_instantiateMVars___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__0___redArg(x_1, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1_spec__1_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_sub(x_2, x_13);
x_15 = lean_array_uget(x_1, x_14);
x_16 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1_spec__1(x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_2 = x_14;
x_4 = x_17;
x_10 = x_18;
goto _start;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1_spec__1_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_22; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_sub(x_2, x_13);
x_22 = lean_array_uget(x_1, x_14);
if (lean_obj_tag(x_22) == 0)
{
x_2 = x_14;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_31; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
x_26 = x_31;
goto block_30;
block_30:
{
lean_object* x_27; 
x_27 = l_Lean_RBNode_findCore___at___Lean_Meta_removeUnused_spec__0___redArg(x_25, x_26);
lean_dec(x_26);
lean_dec(x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_24);
x_2 = x_14;
goto _start;
}
else
{
lean_object* x_29; 
lean_dec(x_27);
x_29 = lean_ctor_get(x_24, 3);
lean_inc(x_29);
lean_dec(x_24);
x_15 = x_29;
goto block_21;
}
}
}
block_21:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_instantiateMVars___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__0___redArg(x_15, x_7, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_CollectFVars_main(x_17, x_4);
x_2 = x_14;
x_4 = x_19;
x_10 = x_18;
goto _start;
}
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_10);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_15 = lean_usize_of_nat(x_11);
x_16 = l_Array_foldrMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1_spec__1_spec__1(x_9, x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_8);
return x_21;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_23 = lean_usize_of_nat(x_19);
x_24 = l_Array_foldrMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1_spec__1_spec__2(x_17, x_22, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
lean_dec(x_15);
x_9 = x_2;
x_10 = x_8;
goto block_13;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_19 = lean_usize_of_nat(x_16);
x_20 = l_Array_foldrMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1_spec__1_spec__2(x_14, x_18, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_9 = x_21;
x_10 = x_22;
goto block_13;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1_spec__1(x_11, x_9, x_3, x_4, x_5, x_6, x_7, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 1);
x_10 = l_Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6_spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_uget(x_2, x_4);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_15);
x_16 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6(x_1, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_17);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
lean_dec(x_15);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_usize_of_nat(x_30);
x_32 = lean_usize_add(x_4, x_31);
x_4 = x_32;
x_5 = x_29;
x_11 = x_26;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
return x_16;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_16, 0);
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_16);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6_spec__7_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_22; 
x_13 = lean_box(0);
x_22 = lean_array_uget(x_1, x_3);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_dec(x_4);
x_14 = x_23;
x_15 = x_10;
goto block_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_107; lean_object* x_118; 
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_118 = lean_ctor_get(x_25, 1);
lean_inc(x_118);
x_107 = x_118;
goto block_117;
block_106:
{
lean_object* x_31; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_30);
x_31 = l_Lean_Meta_isProp(x_30, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_25);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_29);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_35);
x_14 = x_36;
x_15 = x_34;
goto block_21;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l_Lean_instantiateMVars___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__0___redArg(x_30, x_7, x_37);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_26);
x_42 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___redArg(x_26, x_40, x_41);
lean_dec(x_40);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
lean_free_object(x_38);
lean_dec(x_29);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
x_47 = lean_ctor_get(x_42, 0);
lean_dec(x_47);
lean_inc(x_6);
x_48 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_pushDecl(x_26, x_28, x_25, x_6, x_7, x_8, x_9, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 1);
lean_ctor_set(x_49, 1, x_32);
lean_ctor_set(x_49, 0, x_53);
lean_ctor_set(x_42, 1, x_49);
lean_ctor_set(x_42, 0, x_52);
x_14 = x_42;
x_15 = x_50;
goto block_21;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_49, 0);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_49);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_32);
lean_ctor_set(x_42, 1, x_56);
lean_ctor_set(x_42, 0, x_54);
x_14 = x_42;
x_15 = x_50;
goto block_21;
}
}
else
{
uint8_t x_57; 
lean_free_object(x_42);
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_57 = !lean_is_exclusive(x_48);
if (x_57 == 0)
{
return x_48;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_48, 0);
x_59 = lean_ctor_get(x_48, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_48);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_42, 1);
lean_inc(x_61);
lean_dec(x_42);
lean_inc(x_6);
x_62 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_pushDecl(x_26, x_28, x_25, x_6, x_7, x_8, x_9, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_67 = x_63;
} else {
 lean_dec_ref(x_63);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_32);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_68);
x_14 = x_69;
x_15 = x_64;
goto block_21;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_70 = lean_ctor_get(x_62, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_62, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_72 = x_62;
} else {
 lean_dec_ref(x_62);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_32);
lean_dec(x_25);
x_74 = !lean_is_exclusive(x_42);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_42, 1);
x_76 = lean_ctor_get(x_42, 0);
lean_dec(x_76);
lean_ctor_set(x_42, 1, x_29);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_38, 1, x_42);
lean_ctor_set(x_38, 0, x_26);
x_14 = x_38;
x_15 = x_75;
goto block_21;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_42, 1);
lean_inc(x_77);
lean_dec(x_42);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_28);
lean_ctor_set(x_78, 1, x_29);
lean_ctor_set(x_38, 1, x_78);
lean_ctor_set(x_38, 0, x_26);
x_14 = x_38;
x_15 = x_77;
goto block_21;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_ctor_get(x_38, 0);
x_80 = lean_ctor_get(x_38, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_38);
lean_inc(x_26);
x_81 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___redArg(x_26, x_79, x_80);
lean_dec(x_79);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_29);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_85 = x_81;
} else {
 lean_dec_ref(x_81);
 x_85 = lean_box(0);
}
lean_inc(x_6);
x_86 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_pushDecl(x_26, x_28, x_25, x_6, x_7, x_8, x_9, x_84);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_91 = x_87;
} else {
 lean_dec_ref(x_87);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_32);
if (lean_is_scalar(x_85)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_85;
}
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_92);
x_14 = x_93;
x_15 = x_88;
goto block_21;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_85);
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_94 = lean_ctor_get(x_86, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_86, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_96 = x_86;
} else {
 lean_dec_ref(x_86);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_32);
lean_dec(x_25);
x_98 = lean_ctor_get(x_81, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_99 = x_81;
} else {
 lean_dec_ref(x_81);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_28);
lean_ctor_set(x_100, 1, x_29);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_26);
lean_ctor_set(x_101, 1, x_100);
x_14 = x_101;
x_15 = x_98;
goto block_21;
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_102 = !lean_is_exclusive(x_31);
if (x_102 == 0)
{
return x_31;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_31, 0);
x_104 = lean_ctor_get(x_31, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_31);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
block_117:
{
lean_object* x_108; 
x_108 = l_Lean_RBNode_findCore___at___Lean_Meta_removeUnused_spec__0___redArg(x_26, x_107);
lean_dec(x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_25, 3);
lean_inc(x_109);
x_30 = x_109;
goto block_106;
}
else
{
lean_object* x_110; uint8_t x_111; 
lean_dec(x_25);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_dec(x_108);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_110, 1);
lean_dec(x_112);
x_113 = lean_ctor_get(x_110, 0);
lean_dec(x_113);
lean_ctor_set(x_110, 1, x_29);
lean_ctor_set(x_110, 0, x_28);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_26);
lean_ctor_set(x_114, 1, x_110);
x_14 = x_114;
x_15 = x_10;
goto block_21;
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_110);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_28);
lean_ctor_set(x_115, 1, x_29);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_26);
lean_ctor_set(x_116, 1, x_115);
x_14 = x_116;
x_15 = x_10;
goto block_21;
}
}
}
}
block_21:
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_4 = x_16;
x_10 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_22; 
x_13 = lean_box(0);
x_22 = lean_array_uget(x_1, x_3);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_dec(x_4);
x_14 = x_23;
x_15 = x_10;
goto block_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_107; lean_object* x_118; 
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_118 = lean_ctor_get(x_25, 1);
lean_inc(x_118);
x_107 = x_118;
goto block_117;
block_106:
{
lean_object* x_31; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_30);
x_31 = l_Lean_Meta_isProp(x_30, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_25);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_29);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_35);
x_14 = x_36;
x_15 = x_34;
goto block_21;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l_Lean_instantiateMVars___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__0___redArg(x_30, x_7, x_37);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_26);
x_42 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___redArg(x_26, x_40, x_41);
lean_dec(x_40);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
lean_free_object(x_38);
lean_dec(x_29);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
x_47 = lean_ctor_get(x_42, 0);
lean_dec(x_47);
lean_inc(x_6);
x_48 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_pushDecl(x_26, x_28, x_25, x_6, x_7, x_8, x_9, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 1);
lean_ctor_set(x_49, 1, x_32);
lean_ctor_set(x_49, 0, x_53);
lean_ctor_set(x_42, 1, x_49);
lean_ctor_set(x_42, 0, x_52);
x_14 = x_42;
x_15 = x_50;
goto block_21;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_49, 0);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_49);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_32);
lean_ctor_set(x_42, 1, x_56);
lean_ctor_set(x_42, 0, x_54);
x_14 = x_42;
x_15 = x_50;
goto block_21;
}
}
else
{
uint8_t x_57; 
lean_free_object(x_42);
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_57 = !lean_is_exclusive(x_48);
if (x_57 == 0)
{
return x_48;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_48, 0);
x_59 = lean_ctor_get(x_48, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_48);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_42, 1);
lean_inc(x_61);
lean_dec(x_42);
lean_inc(x_6);
x_62 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_pushDecl(x_26, x_28, x_25, x_6, x_7, x_8, x_9, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_67 = x_63;
} else {
 lean_dec_ref(x_63);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_32);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_68);
x_14 = x_69;
x_15 = x_64;
goto block_21;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_70 = lean_ctor_get(x_62, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_62, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_72 = x_62;
} else {
 lean_dec_ref(x_62);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_32);
lean_dec(x_25);
x_74 = !lean_is_exclusive(x_42);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_42, 1);
x_76 = lean_ctor_get(x_42, 0);
lean_dec(x_76);
lean_ctor_set(x_42, 1, x_29);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_38, 1, x_42);
lean_ctor_set(x_38, 0, x_26);
x_14 = x_38;
x_15 = x_75;
goto block_21;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_42, 1);
lean_inc(x_77);
lean_dec(x_42);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_28);
lean_ctor_set(x_78, 1, x_29);
lean_ctor_set(x_38, 1, x_78);
lean_ctor_set(x_38, 0, x_26);
x_14 = x_38;
x_15 = x_77;
goto block_21;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_ctor_get(x_38, 0);
x_80 = lean_ctor_get(x_38, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_38);
lean_inc(x_26);
x_81 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___redArg(x_26, x_79, x_80);
lean_dec(x_79);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_29);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_85 = x_81;
} else {
 lean_dec_ref(x_81);
 x_85 = lean_box(0);
}
lean_inc(x_6);
x_86 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_pushDecl(x_26, x_28, x_25, x_6, x_7, x_8, x_9, x_84);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_91 = x_87;
} else {
 lean_dec_ref(x_87);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_32);
if (lean_is_scalar(x_85)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_85;
}
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_92);
x_14 = x_93;
x_15 = x_88;
goto block_21;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_85);
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_94 = lean_ctor_get(x_86, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_86, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_96 = x_86;
} else {
 lean_dec_ref(x_86);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_32);
lean_dec(x_25);
x_98 = lean_ctor_get(x_81, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_99 = x_81;
} else {
 lean_dec_ref(x_81);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_28);
lean_ctor_set(x_100, 1, x_29);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_26);
lean_ctor_set(x_101, 1, x_100);
x_14 = x_101;
x_15 = x_98;
goto block_21;
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_102 = !lean_is_exclusive(x_31);
if (x_102 == 0)
{
return x_31;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_31, 0);
x_104 = lean_ctor_get(x_31, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_31);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
block_117:
{
lean_object* x_108; 
x_108 = l_Lean_RBNode_findCore___at___Lean_Meta_removeUnused_spec__0___redArg(x_26, x_107);
lean_dec(x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_25, 3);
lean_inc(x_109);
x_30 = x_109;
goto block_106;
}
else
{
lean_object* x_110; uint8_t x_111; 
lean_dec(x_25);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_dec(x_108);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_110, 1);
lean_dec(x_112);
x_113 = lean_ctor_get(x_110, 0);
lean_dec(x_113);
lean_ctor_set(x_110, 1, x_29);
lean_ctor_set(x_110, 0, x_28);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_26);
lean_ctor_set(x_114, 1, x_110);
x_14 = x_114;
x_15 = x_10;
goto block_21;
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_110);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_28);
lean_ctor_set(x_115, 1, x_29);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_26);
lean_ctor_set(x_116, 1, x_115);
x_14 = x_116;
x_15 = x_10;
goto block_21;
}
}
}
}
block_21:
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_3, x_18);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6_spec__7_spec__7(x_1, x_2, x_19, x_16, x_5, x_6, x_7, x_8, x_9, x_15);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_array_size(x_11);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_usize_of_nat(x_15);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6_spec__6(x_1, x_11, x_14, x_16, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_22);
lean_ctor_set(x_17, 0, x_2);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_18);
lean_free_object(x_2);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_28);
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec(x_19);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_free_object(x_2);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; lean_object* x_40; size_t x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
lean_dec(x_2);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_3);
x_39 = lean_array_size(x_36);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_usize_of_nat(x_40);
x_42 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6_spec__6(x_1, x_36, x_39, x_41, x_38, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_36);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_46 = x_42;
} else {
 lean_dec_ref(x_42);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_43);
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_51 = x_42;
} else {
 lean_dec_ref(x_42);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_44, 0);
lean_inc(x_52);
lean_dec(x_44);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_42, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_42, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_56 = x_42;
} else {
 lean_dec_ref(x_42);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_2);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; lean_object* x_63; size_t x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_2, 0);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_3);
x_62 = lean_array_size(x_59);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_usize_of_nat(x_63);
x_65 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6_spec__7(x_59, x_62, x_64, x_61, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_59);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_65);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_65, 0);
lean_dec(x_69);
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec(x_66);
lean_ctor_set(x_2, 0, x_70);
lean_ctor_set(x_65, 0, x_2);
return x_65;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
lean_dec(x_65);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_dec(x_66);
lean_ctor_set(x_2, 0, x_72);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_2);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_66);
lean_free_object(x_2);
x_74 = !lean_is_exclusive(x_65);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_65, 0);
lean_dec(x_75);
x_76 = lean_ctor_get(x_67, 0);
lean_inc(x_76);
lean_dec(x_67);
lean_ctor_set(x_65, 0, x_76);
return x_65;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_65, 1);
lean_inc(x_77);
lean_dec(x_65);
x_78 = lean_ctor_get(x_67, 0);
lean_inc(x_78);
lean_dec(x_67);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_free_object(x_2);
x_80 = !lean_is_exclusive(x_65);
if (x_80 == 0)
{
return x_65;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_65, 0);
x_82 = lean_ctor_get(x_65, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_65);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; size_t x_87; lean_object* x_88; size_t x_89; lean_object* x_90; 
x_84 = lean_ctor_get(x_2, 0);
lean_inc(x_84);
lean_dec(x_2);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_3);
x_87 = lean_array_size(x_84);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_usize_of_nat(x_88);
x_90 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6_spec__7(x_84, x_87, x_89, x_86, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_84);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_94 = x_90;
} else {
 lean_dec_ref(x_90);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
lean_dec(x_91);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
if (lean_is_scalar(x_94)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_94;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_93);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_91);
x_98 = lean_ctor_get(x_90, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_99 = x_90;
} else {
 lean_dec_ref(x_90);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_92, 0);
lean_inc(x_100);
lean_dec(x_92);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_90, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_90, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_104 = x_90;
} else {
 lean_dec_ref(x_90);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__10_spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_22; 
x_13 = lean_box(0);
x_22 = lean_array_uget(x_1, x_3);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_dec(x_4);
x_14 = x_23;
x_15 = x_10;
goto block_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_107; lean_object* x_118; 
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_118 = lean_ctor_get(x_25, 1);
lean_inc(x_118);
x_107 = x_118;
goto block_117;
block_106:
{
lean_object* x_31; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_30);
x_31 = l_Lean_Meta_isProp(x_30, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_25);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_29);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_35);
x_14 = x_36;
x_15 = x_34;
goto block_21;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l_Lean_instantiateMVars___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__0___redArg(x_30, x_7, x_37);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_26);
x_42 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___redArg(x_26, x_40, x_41);
lean_dec(x_40);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
lean_free_object(x_38);
lean_dec(x_29);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
x_47 = lean_ctor_get(x_42, 0);
lean_dec(x_47);
lean_inc(x_6);
x_48 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_pushDecl(x_26, x_28, x_25, x_6, x_7, x_8, x_9, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 1);
lean_ctor_set(x_49, 1, x_32);
lean_ctor_set(x_49, 0, x_53);
lean_ctor_set(x_42, 1, x_49);
lean_ctor_set(x_42, 0, x_52);
x_14 = x_42;
x_15 = x_50;
goto block_21;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_49, 0);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_49);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_32);
lean_ctor_set(x_42, 1, x_56);
lean_ctor_set(x_42, 0, x_54);
x_14 = x_42;
x_15 = x_50;
goto block_21;
}
}
else
{
uint8_t x_57; 
lean_free_object(x_42);
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_57 = !lean_is_exclusive(x_48);
if (x_57 == 0)
{
return x_48;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_48, 0);
x_59 = lean_ctor_get(x_48, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_48);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_42, 1);
lean_inc(x_61);
lean_dec(x_42);
lean_inc(x_6);
x_62 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_pushDecl(x_26, x_28, x_25, x_6, x_7, x_8, x_9, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_67 = x_63;
} else {
 lean_dec_ref(x_63);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_32);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_68);
x_14 = x_69;
x_15 = x_64;
goto block_21;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_70 = lean_ctor_get(x_62, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_62, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_72 = x_62;
} else {
 lean_dec_ref(x_62);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_32);
lean_dec(x_25);
x_74 = !lean_is_exclusive(x_42);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_42, 1);
x_76 = lean_ctor_get(x_42, 0);
lean_dec(x_76);
lean_ctor_set(x_42, 1, x_29);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_38, 1, x_42);
lean_ctor_set(x_38, 0, x_26);
x_14 = x_38;
x_15 = x_75;
goto block_21;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_42, 1);
lean_inc(x_77);
lean_dec(x_42);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_28);
lean_ctor_set(x_78, 1, x_29);
lean_ctor_set(x_38, 1, x_78);
lean_ctor_set(x_38, 0, x_26);
x_14 = x_38;
x_15 = x_77;
goto block_21;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_ctor_get(x_38, 0);
x_80 = lean_ctor_get(x_38, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_38);
lean_inc(x_26);
x_81 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___redArg(x_26, x_79, x_80);
lean_dec(x_79);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_29);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_85 = x_81;
} else {
 lean_dec_ref(x_81);
 x_85 = lean_box(0);
}
lean_inc(x_6);
x_86 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_pushDecl(x_26, x_28, x_25, x_6, x_7, x_8, x_9, x_84);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_91 = x_87;
} else {
 lean_dec_ref(x_87);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_32);
if (lean_is_scalar(x_85)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_85;
}
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_92);
x_14 = x_93;
x_15 = x_88;
goto block_21;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_85);
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_94 = lean_ctor_get(x_86, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_86, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_96 = x_86;
} else {
 lean_dec_ref(x_86);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_32);
lean_dec(x_25);
x_98 = lean_ctor_get(x_81, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_99 = x_81;
} else {
 lean_dec_ref(x_81);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_28);
lean_ctor_set(x_100, 1, x_29);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_26);
lean_ctor_set(x_101, 1, x_100);
x_14 = x_101;
x_15 = x_98;
goto block_21;
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_102 = !lean_is_exclusive(x_31);
if (x_102 == 0)
{
return x_31;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_31, 0);
x_104 = lean_ctor_get(x_31, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_31);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
block_117:
{
lean_object* x_108; 
x_108 = l_Lean_RBNode_findCore___at___Lean_Meta_removeUnused_spec__0___redArg(x_26, x_107);
lean_dec(x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_25, 3);
lean_inc(x_109);
x_30 = x_109;
goto block_106;
}
else
{
lean_object* x_110; uint8_t x_111; 
lean_dec(x_25);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_dec(x_108);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_110, 1);
lean_dec(x_112);
x_113 = lean_ctor_get(x_110, 0);
lean_dec(x_113);
lean_ctor_set(x_110, 1, x_29);
lean_ctor_set(x_110, 0, x_28);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_26);
lean_ctor_set(x_114, 1, x_110);
x_14 = x_114;
x_15 = x_10;
goto block_21;
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_110);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_28);
lean_ctor_set(x_115, 1, x_29);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_26);
lean_ctor_set(x_116, 1, x_115);
x_14 = x_116;
x_15 = x_10;
goto block_21;
}
}
}
}
block_21:
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_4 = x_16;
x_10 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_22; 
x_13 = lean_box(0);
x_22 = lean_array_uget(x_1, x_3);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_dec(x_4);
x_14 = x_23;
x_15 = x_10;
goto block_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_107; lean_object* x_118; 
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_118 = lean_ctor_get(x_25, 1);
lean_inc(x_118);
x_107 = x_118;
goto block_117;
block_106:
{
lean_object* x_31; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_30);
x_31 = l_Lean_Meta_isProp(x_30, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_25);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_29);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_35);
x_14 = x_36;
x_15 = x_34;
goto block_21;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l_Lean_instantiateMVars___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__0___redArg(x_30, x_7, x_37);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_26);
x_42 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___redArg(x_26, x_40, x_41);
lean_dec(x_40);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
lean_free_object(x_38);
lean_dec(x_29);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
x_47 = lean_ctor_get(x_42, 0);
lean_dec(x_47);
lean_inc(x_6);
x_48 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_pushDecl(x_26, x_28, x_25, x_6, x_7, x_8, x_9, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 1);
lean_ctor_set(x_49, 1, x_32);
lean_ctor_set(x_49, 0, x_53);
lean_ctor_set(x_42, 1, x_49);
lean_ctor_set(x_42, 0, x_52);
x_14 = x_42;
x_15 = x_50;
goto block_21;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_49, 0);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_49);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_32);
lean_ctor_set(x_42, 1, x_56);
lean_ctor_set(x_42, 0, x_54);
x_14 = x_42;
x_15 = x_50;
goto block_21;
}
}
else
{
uint8_t x_57; 
lean_free_object(x_42);
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_57 = !lean_is_exclusive(x_48);
if (x_57 == 0)
{
return x_48;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_48, 0);
x_59 = lean_ctor_get(x_48, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_48);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_42, 1);
lean_inc(x_61);
lean_dec(x_42);
lean_inc(x_6);
x_62 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_pushDecl(x_26, x_28, x_25, x_6, x_7, x_8, x_9, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_67 = x_63;
} else {
 lean_dec_ref(x_63);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_32);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_68);
x_14 = x_69;
x_15 = x_64;
goto block_21;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_70 = lean_ctor_get(x_62, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_62, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_72 = x_62;
} else {
 lean_dec_ref(x_62);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_32);
lean_dec(x_25);
x_74 = !lean_is_exclusive(x_42);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_42, 1);
x_76 = lean_ctor_get(x_42, 0);
lean_dec(x_76);
lean_ctor_set(x_42, 1, x_29);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_38, 1, x_42);
lean_ctor_set(x_38, 0, x_26);
x_14 = x_38;
x_15 = x_75;
goto block_21;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_42, 1);
lean_inc(x_77);
lean_dec(x_42);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_28);
lean_ctor_set(x_78, 1, x_29);
lean_ctor_set(x_38, 1, x_78);
lean_ctor_set(x_38, 0, x_26);
x_14 = x_38;
x_15 = x_77;
goto block_21;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_ctor_get(x_38, 0);
x_80 = lean_ctor_get(x_38, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_38);
lean_inc(x_26);
x_81 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_isIrrelevant___redArg(x_26, x_79, x_80);
lean_dec(x_79);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_29);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_85 = x_81;
} else {
 lean_dec_ref(x_81);
 x_85 = lean_box(0);
}
lean_inc(x_6);
x_86 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_pushDecl(x_26, x_28, x_25, x_6, x_7, x_8, x_9, x_84);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_91 = x_87;
} else {
 lean_dec_ref(x_87);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_32);
if (lean_is_scalar(x_85)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_85;
}
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_92);
x_14 = x_93;
x_15 = x_88;
goto block_21;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_85);
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_94 = lean_ctor_get(x_86, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_86, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_96 = x_86;
} else {
 lean_dec_ref(x_86);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_32);
lean_dec(x_25);
x_98 = lean_ctor_get(x_81, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_99 = x_81;
} else {
 lean_dec_ref(x_81);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_28);
lean_ctor_set(x_100, 1, x_29);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_26);
lean_ctor_set(x_101, 1, x_100);
x_14 = x_101;
x_15 = x_98;
goto block_21;
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_102 = !lean_is_exclusive(x_31);
if (x_102 == 0)
{
return x_31;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_31, 0);
x_104 = lean_ctor_get(x_31, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_31);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
block_117:
{
lean_object* x_108; 
x_108 = l_Lean_RBNode_findCore___at___Lean_Meta_removeUnused_spec__0___redArg(x_26, x_107);
lean_dec(x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_25, 3);
lean_inc(x_109);
x_30 = x_109;
goto block_106;
}
else
{
lean_object* x_110; uint8_t x_111; 
lean_dec(x_25);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_dec(x_108);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_110, 1);
lean_dec(x_112);
x_113 = lean_ctor_get(x_110, 0);
lean_dec(x_113);
lean_ctor_set(x_110, 1, x_29);
lean_ctor_set(x_110, 0, x_28);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_26);
lean_ctor_set(x_114, 1, x_110);
x_14 = x_114;
x_15 = x_10;
goto block_21;
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_110);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_28);
lean_ctor_set(x_115, 1, x_29);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_26);
lean_ctor_set(x_116, 1, x_115);
x_14 = x_116;
x_15 = x_10;
goto block_21;
}
}
}
}
block_21:
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_3, x_18);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__10_spec__10(x_1, x_2, x_19, x_16, x_5, x_6, x_7, x_8, x_9, x_15);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_10 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6(x_2, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; size_t x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_array_size(x_20);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_usize_of_nat(x_24);
x_26 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__10(x_20, x_23, x_25, x_22, x_3, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_27);
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_26, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_37);
return x_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_dec(x_26);
x_39 = lean_ctor_get(x_28, 0);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_26);
if (x_41 == 0)
{
return x_26;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_26, 0);
x_43 = lean_ctor_get(x_26, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_26);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_10);
if (x_45 == 0)
{
return x_10;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_10, 0);
x_47 = lean_ctor_get(x_10, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_10);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_box(0);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6(x_15, x_14, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_1 = x_17;
x_7 = x_21;
goto _start;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__14___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__14___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__14___redArg___lam__0), 7, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_withContext___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__14___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_MVarId_getType_x27(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(8u);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_shiftl(x_11, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_17 = l_Nat_nextPowerOfTwo(x_16);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = lean_mk_array(x_17, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(0);
x_22 = lean_mk_empty_array_with_capacity(x_12);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
lean_inc(x_9);
x_24 = l_Lean_CollectFVars_main(x_9, x_23);
x_25 = lean_ctor_get(x_3, 2);
lean_inc(x_25);
x_26 = l_Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1(x_25, x_24, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_30);
x_31 = l_Lean_RBTree_toArray___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps_spec__0(x_30);
lean_inc(x_3);
x_32 = l_Lean_Meta_sortFVarIds___redArg(x_31, x_3, x_29);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 1);
x_35 = lean_box(0);
lean_ctor_set(x_32, 1, x_35);
lean_ctor_set(x_26, 1, x_32);
lean_ctor_set(x_26, 0, x_30);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_36 = l_Lean_Loop_forIn_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__13(x_26, x_2, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_array_size(x_40);
x_42 = lean_usize_of_nat(x_12);
x_43 = l_Array_mapMUnsafe_map___at___Lean_LocalContext_getFVars_spec__0(x_41, x_42, x_40);
x_44 = lean_box(1);
x_45 = lean_box(1);
x_46 = lean_unbox(x_35);
x_47 = lean_unbox(x_44);
x_48 = lean_unbox(x_45);
x_49 = l_Lean_Meta_mkForallFVars(x_43, x_9, x_46, x_47, x_48, x_3, x_4, x_5, x_6, x_39);
lean_dec(x_43);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Elab_Eqns_simpEqnType(x_50, x_3, x_4, x_5, x_6, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_st_ref_take(x_2, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_array_push(x_56, x_53);
x_59 = lean_st_ref_set(x_2, x_58, x_57);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
x_62 = lean_box(0);
lean_ctor_set(x_59, 0, x_62);
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_52);
if (x_66 == 0)
{
return x_52;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_52, 0);
x_68 = lean_ctor_get(x_52, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_52);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_49);
if (x_70 == 0)
{
return x_49;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_49, 0);
x_72 = lean_ctor_get(x_49, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_49);
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
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_36);
if (x_74 == 0)
{
return x_36;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_36, 0);
x_76 = lean_ctor_get(x_36, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_36);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_32, 0);
x_79 = lean_ctor_get(x_32, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_32);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_26, 1, x_81);
lean_ctor_set(x_26, 0, x_30);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_82 = l_Lean_Loop_forIn_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__13(x_26, x_2, x_3, x_4, x_5, x_6, x_79);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; size_t x_87; size_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; lean_object* x_95; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_array_size(x_86);
x_88 = lean_usize_of_nat(x_12);
x_89 = l_Array_mapMUnsafe_map___at___Lean_LocalContext_getFVars_spec__0(x_87, x_88, x_86);
x_90 = lean_box(1);
x_91 = lean_box(1);
x_92 = lean_unbox(x_80);
x_93 = lean_unbox(x_90);
x_94 = lean_unbox(x_91);
x_95 = l_Lean_Meta_mkForallFVars(x_89, x_9, x_92, x_93, x_94, x_3, x_4, x_5, x_6, x_85);
lean_dec(x_89);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lean_Elab_Eqns_simpEqnType(x_96, x_3, x_4, x_5, x_6, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_st_ref_take(x_2, x_100);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_array_push(x_102, x_99);
x_105 = lean_st_ref_set(x_2, x_104, x_103);
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
x_108 = lean_box(0);
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_106);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_98, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_98, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_112 = x_98;
} else {
 lean_dec_ref(x_98);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_114 = lean_ctor_get(x_95, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_95, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_116 = x_95;
} else {
 lean_dec_ref(x_95);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_118 = lean_ctor_get(x_82, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_82, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_120 = x_82;
} else {
 lean_dec_ref(x_82);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_122 = lean_ctor_get(x_26, 0);
x_123 = lean_ctor_get(x_26, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_26);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
lean_inc(x_124);
x_125 = l_Lean_RBTree_toArray___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_collectDeps_spec__0(x_124);
lean_inc(x_3);
x_126 = l_Lean_Meta_sortFVarIds___redArg(x_125, x_3, x_123);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_129 = x_126;
} else {
 lean_dec_ref(x_126);
 x_129 = lean_box(0);
}
x_130 = lean_box(0);
if (lean_is_scalar(x_129)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_129;
}
lean_ctor_set(x_131, 0, x_127);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_124);
lean_ctor_set(x_132, 1, x_131);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_133 = l_Lean_Loop_forIn_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__13(x_132, x_2, x_3, x_4, x_5, x_6, x_128);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; size_t x_138; size_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; lean_object* x_146; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_array_size(x_137);
x_139 = lean_usize_of_nat(x_12);
x_140 = l_Array_mapMUnsafe_map___at___Lean_LocalContext_getFVars_spec__0(x_138, x_139, x_137);
x_141 = lean_box(1);
x_142 = lean_box(1);
x_143 = lean_unbox(x_130);
x_144 = lean_unbox(x_141);
x_145 = lean_unbox(x_142);
x_146 = l_Lean_Meta_mkForallFVars(x_140, x_9, x_143, x_144, x_145, x_3, x_4, x_5, x_6, x_136);
lean_dec(x_140);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l_Lean_Elab_Eqns_simpEqnType(x_147, x_3, x_4, x_5, x_6, x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_st_ref_take(x_2, x_151);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_array_push(x_153, x_150);
x_156 = lean_st_ref_set(x_2, x_155, x_154);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
x_159 = lean_box(0);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_157);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_149, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_149, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_163 = x_149;
} else {
 lean_dec_ref(x_149);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_165 = lean_ctor_get(x_146, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_146, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_167 = x_146;
} else {
 lean_dec_ref(x_146);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_169 = lean_ctor_get(x_133, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_133, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_171 = x_133;
} else {
 lean_dec_ref(x_133);
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
}
else
{
uint8_t x_173; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_173 = !lean_is_exclusive(x_8);
if (x_173 == 0)
{
return x_8;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_8, 0);
x_175 = lean_ctor_get(x_8, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_8);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn___lam__0___boxed), 7, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__14___redArg(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_instantiateMVars___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldrMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1_spec__1_spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldrMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1_spec__1_spec__2(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PersistentArray_foldrM___at___Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_LocalContext_foldrM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6_spec__6(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6_spec__7_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6_spec__7_spec__7(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6_spec__7(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__10_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__10_spec__10(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6_spec__10(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PersistentArray_forIn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Loop_forIn_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__14___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__14___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_withContext___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn_spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_array_uget(x_13, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lean_Meta_isConstructorApp(x_14, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_box(0);
x_20 = lean_unbox(x_17);
lean_dec(x_17);
if (x_20 == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; 
lean_free_object(x_15);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_add(x_3, x_22);
x_3 = x_23;
x_4 = x_19;
x_9 = x_18;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_15, 0, x_25);
return x_15;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_box(0);
x_29 = lean_unbox(x_26);
lean_dec(x_26);
if (x_29 == 0)
{
lean_object* x_30; size_t x_31; size_t x_32; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_usize_of_nat(x_30);
x_32 = lean_usize_add(x_3, x_31);
x_3 = x_32;
x_4 = x_28;
x_9 = x_27;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
return x_15;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_15);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_12 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1(x_1, x_3, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1(x_1, x_4, x_6, x_7, x_8, x_9, x_10, x_14);
return x_15;
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_20; uint8_t x_21; 
x_20 = lean_st_ref_get(x_3, x_8);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; lean_object* x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_93; size_t x_98; size_t x_99; lean_object* x_100; lean_object* x_101; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_get_size(x_24);
x_26 = l_Lean_Expr_hash(x_2);
x_27 = lean_unsigned_to_nat(32u);
x_28 = lean_uint64_of_nat(x_27);
x_29 = lean_uint64_shift_right(x_26, x_28);
x_30 = lean_uint64_xor(x_26, x_29);
x_31 = lean_unsigned_to_nat(16u);
x_32 = lean_uint64_of_nat(x_31);
x_33 = lean_uint64_shift_right(x_30, x_32);
x_34 = lean_uint64_xor(x_30, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_usize_of_nat(x_37);
x_98 = lean_usize_sub(x_36, x_38);
x_99 = lean_usize_land(x_35, x_98);
x_100 = lean_array_uget(x_24, x_99);
lean_dec(x_24);
x_101 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_reduce_visit_spec__0___redArg(x_2, x_100);
lean_dec(x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
lean_free_object(x_20);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_102 = lean_apply_6(x_1, x_2, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
uint8_t x_104; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_102);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_102, 0);
lean_dec(x_105);
x_106 = !lean_is_exclusive(x_103);
if (x_106 == 0)
{
return x_102;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_103, 0);
lean_inc(x_107);
lean_dec(x_103);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_102, 0, x_108);
return x_102;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_ctor_get(x_102, 1);
lean_inc(x_109);
lean_dec(x_102);
x_110 = lean_ctor_get(x_103, 0);
lean_inc(x_110);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_111 = x_103;
} else {
 lean_dec_ref(x_103);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 1, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_110);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_109);
return x_113;
}
}
else
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_103, 0);
lean_inc(x_114);
lean_dec(x_103);
x_115 = lean_unbox(x_114);
lean_dec(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_116 = lean_ctor_get(x_102, 1);
lean_inc(x_116);
lean_dec(x_102);
x_117 = lean_box(0);
x_39 = x_117;
x_40 = x_116;
goto block_92;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_102, 1);
lean_inc(x_118);
lean_dec(x_102);
x_119 = lean_ctor_get(x_2, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_2, 1);
lean_inc(x_120);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_121 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1(x_1, x_119, x_3, x_4, x_5, x_6, x_7, x_118);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_obj_tag(x_122) == 0)
{
lean_dec(x_122);
lean_dec(x_120);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_93 = x_121;
goto block_97;
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1(x_1, x_120, x_3, x_4, x_5, x_6, x_7, x_123);
x_93 = x_124;
goto block_97;
}
}
else
{
lean_dec(x_120);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_93 = x_121;
goto block_97;
}
}
case 6:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; 
x_125 = lean_ctor_get(x_102, 1);
lean_inc(x_125);
lean_dec(x_102);
x_126 = lean_ctor_get(x_2, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_2, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_2, 2);
lean_inc(x_128);
x_129 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_130 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1___lam__0(x_1, x_126, x_127, x_128, x_129, x_3, x_4, x_5, x_6, x_7, x_125);
lean_dec(x_126);
x_93 = x_130;
goto block_97;
}
case 7:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; 
x_131 = lean_ctor_get(x_102, 1);
lean_inc(x_131);
lean_dec(x_102);
x_132 = lean_ctor_get(x_2, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_2, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_2, 2);
lean_inc(x_134);
x_135 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_136 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1___lam__0(x_1, x_132, x_133, x_134, x_135, x_3, x_4, x_5, x_6, x_7, x_131);
lean_dec(x_132);
x_93 = x_136;
goto block_97;
}
case 8:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_ctor_get(x_102, 1);
lean_inc(x_137);
lean_dec(x_102);
x_138 = lean_ctor_get(x_2, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_2, 2);
lean_inc(x_139);
x_140 = lean_ctor_get(x_2, 3);
lean_inc(x_140);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_141 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1(x_1, x_138, x_3, x_4, x_5, x_6, x_7, x_137);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
if (lean_obj_tag(x_142) == 0)
{
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_93 = x_141;
goto block_97;
}
else
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_144 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1(x_1, x_139, x_3, x_4, x_5, x_6, x_7, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
if (lean_obj_tag(x_145) == 0)
{
lean_dec(x_145);
lean_dec(x_140);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_93 = x_144;
goto block_97;
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1(x_1, x_140, x_3, x_4, x_5, x_6, x_7, x_146);
x_93 = x_147;
goto block_97;
}
}
else
{
lean_dec(x_140);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_93 = x_144;
goto block_97;
}
}
}
else
{
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_93 = x_141;
goto block_97;
}
}
case 10:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_102, 1);
lean_inc(x_148);
lean_dec(x_102);
x_149 = lean_ctor_get(x_2, 1);
lean_inc(x_149);
x_150 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1(x_1, x_149, x_3, x_4, x_5, x_6, x_7, x_148);
x_93 = x_150;
goto block_97;
}
case 11:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_102, 1);
lean_inc(x_151);
lean_dec(x_102);
x_152 = lean_ctor_get(x_2, 2);
lean_inc(x_152);
x_153 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1(x_1, x_152, x_3, x_4, x_5, x_6, x_7, x_151);
x_93 = x_153;
goto block_97;
}
default: 
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_154 = lean_ctor_get(x_102, 1);
lean_inc(x_154);
lean_dec(x_102);
x_155 = lean_box(0);
x_39 = x_155;
x_40 = x_154;
goto block_92;
}
}
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_102);
if (x_156 == 0)
{
return x_102;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_102, 0);
x_158 = lean_ctor_get(x_102, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_102);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_160 = !lean_is_exclusive(x_101);
if (x_160 == 0)
{
lean_ctor_set(x_20, 0, x_101);
return x_20;
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_101, 0);
lean_inc(x_161);
lean_dec(x_101);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_20, 0, x_162);
return x_20;
}
}
block_92:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_st_ref_take(x_3, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; size_t x_50; lean_object* x_51; uint8_t x_52; 
x_45 = lean_ctor_get(x_42, 0);
x_46 = lean_ctor_get(x_42, 1);
x_47 = lean_array_get_size(x_46);
x_48 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_49 = lean_usize_sub(x_48, x_38);
x_50 = lean_usize_land(x_35, x_49);
x_51 = lean_array_uget(x_46, x_50);
x_52 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelMVars_visitExpr_spec__0___redArg(x_2, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_53 = lean_nat_add(x_45, x_37);
lean_dec(x_45);
lean_inc(x_39);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_2);
lean_ctor_set(x_54, 1, x_39);
lean_ctor_set(x_54, 2, x_51);
x_55 = lean_array_uset(x_46, x_50, x_54);
x_56 = lean_unsigned_to_nat(2u);
x_57 = lean_nat_shiftl(x_53, x_56);
x_58 = lean_unsigned_to_nat(3u);
x_59 = lean_nat_div(x_57, x_58);
lean_dec(x_57);
x_60 = lean_array_get_size(x_55);
x_61 = lean_nat_dec_le(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelMVars_visitExpr_spec__1___redArg(x_55);
lean_ctor_set(x_42, 1, x_62);
lean_ctor_set(x_42, 0, x_53);
x_9 = x_39;
x_10 = x_43;
x_11 = x_42;
goto block_19;
}
else
{
lean_ctor_set(x_42, 1, x_55);
lean_ctor_set(x_42, 0, x_53);
x_9 = x_39;
x_10 = x_43;
x_11 = x_42;
goto block_19;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_box(0);
x_64 = lean_array_uset(x_46, x_50, x_63);
lean_inc(x_39);
x_65 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_reduce_visit_spec__6___redArg(x_2, x_39, x_51);
x_66 = lean_array_uset(x_64, x_50, x_65);
lean_ctor_set(x_42, 1, x_66);
x_9 = x_39;
x_10 = x_43;
x_11 = x_42;
goto block_19;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; size_t x_72; lean_object* x_73; uint8_t x_74; 
x_67 = lean_ctor_get(x_42, 0);
x_68 = lean_ctor_get(x_42, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_42);
x_69 = lean_array_get_size(x_68);
x_70 = lean_usize_of_nat(x_69);
lean_dec(x_69);
x_71 = lean_usize_sub(x_70, x_38);
x_72 = lean_usize_land(x_35, x_71);
x_73 = lean_array_uget(x_68, x_72);
x_74 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelMVars_visitExpr_spec__0___redArg(x_2, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_75 = lean_nat_add(x_67, x_37);
lean_dec(x_67);
lean_inc(x_39);
x_76 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_76, 0, x_2);
lean_ctor_set(x_76, 1, x_39);
lean_ctor_set(x_76, 2, x_73);
x_77 = lean_array_uset(x_68, x_72, x_76);
x_78 = lean_unsigned_to_nat(2u);
x_79 = lean_nat_shiftl(x_75, x_78);
x_80 = lean_unsigned_to_nat(3u);
x_81 = lean_nat_div(x_79, x_80);
lean_dec(x_79);
x_82 = lean_array_get_size(x_77);
x_83 = lean_nat_dec_le(x_81, x_82);
lean_dec(x_82);
lean_dec(x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelMVars_visitExpr_spec__1___redArg(x_77);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_75);
lean_ctor_set(x_85, 1, x_84);
x_9 = x_39;
x_10 = x_43;
x_11 = x_85;
goto block_19;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_75);
lean_ctor_set(x_86, 1, x_77);
x_9 = x_39;
x_10 = x_43;
x_11 = x_86;
goto block_19;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_box(0);
x_88 = lean_array_uset(x_68, x_72, x_87);
lean_inc(x_39);
x_89 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_reduce_visit_spec__6___redArg(x_2, x_39, x_73);
x_90 = lean_array_uset(x_88, x_72, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_67);
lean_ctor_set(x_91, 1, x_90);
x_9 = x_39;
x_10 = x_43;
x_11 = x_91;
goto block_19;
}
}
}
block_97:
{
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
lean_dec(x_94);
lean_dec(x_2);
return x_93;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec(x_94);
x_39 = x_96;
x_40 = x_95;
goto block_92;
}
}
else
{
lean_dec(x_2);
return x_93;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint64_t x_167; lean_object* x_168; uint64_t x_169; uint64_t x_170; uint64_t x_171; lean_object* x_172; uint64_t x_173; uint64_t x_174; uint64_t x_175; size_t x_176; size_t x_177; lean_object* x_178; size_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_212; size_t x_217; size_t x_218; lean_object* x_219; lean_object* x_220; 
x_163 = lean_ctor_get(x_20, 0);
x_164 = lean_ctor_get(x_20, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_20);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_array_get_size(x_165);
x_167 = l_Lean_Expr_hash(x_2);
x_168 = lean_unsigned_to_nat(32u);
x_169 = lean_uint64_of_nat(x_168);
x_170 = lean_uint64_shift_right(x_167, x_169);
x_171 = lean_uint64_xor(x_167, x_170);
x_172 = lean_unsigned_to_nat(16u);
x_173 = lean_uint64_of_nat(x_172);
x_174 = lean_uint64_shift_right(x_171, x_173);
x_175 = lean_uint64_xor(x_171, x_174);
x_176 = lean_uint64_to_usize(x_175);
x_177 = lean_usize_of_nat(x_166);
lean_dec(x_166);
x_178 = lean_unsigned_to_nat(1u);
x_179 = lean_usize_of_nat(x_178);
x_217 = lean_usize_sub(x_177, x_179);
x_218 = lean_usize_land(x_176, x_217);
x_219 = lean_array_uget(x_165, x_218);
lean_dec(x_165);
x_220 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_reduce_visit_spec__0___redArg(x_2, x_219);
lean_dec(x_219);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; 
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_221 = lean_apply_6(x_1, x_2, x_4, x_5, x_6, x_7, x_164);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_224 = x_221;
} else {
 lean_dec_ref(x_221);
 x_224 = lean_box(0);
}
x_225 = lean_ctor_get(x_222, 0);
lean_inc(x_225);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 x_226 = x_222;
} else {
 lean_dec_ref(x_222);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(0, 1, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_225);
if (lean_is_scalar(x_224)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_224;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_223);
return x_228;
}
else
{
lean_object* x_229; uint8_t x_230; 
x_229 = lean_ctor_get(x_222, 0);
lean_inc(x_229);
lean_dec(x_222);
x_230 = lean_unbox(x_229);
lean_dec(x_229);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_231 = lean_ctor_get(x_221, 1);
lean_inc(x_231);
lean_dec(x_221);
x_232 = lean_box(0);
x_180 = x_232;
x_181 = x_231;
goto block_211;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_233 = lean_ctor_get(x_221, 1);
lean_inc(x_233);
lean_dec(x_221);
x_234 = lean_ctor_get(x_2, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_2, 1);
lean_inc(x_235);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_236 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1(x_1, x_234, x_3, x_4, x_5, x_6, x_7, x_233);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
if (lean_obj_tag(x_237) == 0)
{
lean_dec(x_237);
lean_dec(x_235);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_212 = x_236;
goto block_216;
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1(x_1, x_235, x_3, x_4, x_5, x_6, x_7, x_238);
x_212 = x_239;
goto block_216;
}
}
else
{
lean_dec(x_235);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_212 = x_236;
goto block_216;
}
}
case 6:
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; 
x_240 = lean_ctor_get(x_221, 1);
lean_inc(x_240);
lean_dec(x_221);
x_241 = lean_ctor_get(x_2, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_2, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_2, 2);
lean_inc(x_243);
x_244 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_245 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1___lam__0(x_1, x_241, x_242, x_243, x_244, x_3, x_4, x_5, x_6, x_7, x_240);
lean_dec(x_241);
x_212 = x_245;
goto block_216;
}
case 7:
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; 
x_246 = lean_ctor_get(x_221, 1);
lean_inc(x_246);
lean_dec(x_221);
x_247 = lean_ctor_get(x_2, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_2, 1);
lean_inc(x_248);
x_249 = lean_ctor_get(x_2, 2);
lean_inc(x_249);
x_250 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_251 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1___lam__0(x_1, x_247, x_248, x_249, x_250, x_3, x_4, x_5, x_6, x_7, x_246);
lean_dec(x_247);
x_212 = x_251;
goto block_216;
}
case 8:
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_252 = lean_ctor_get(x_221, 1);
lean_inc(x_252);
lean_dec(x_221);
x_253 = lean_ctor_get(x_2, 1);
lean_inc(x_253);
x_254 = lean_ctor_get(x_2, 2);
lean_inc(x_254);
x_255 = lean_ctor_get(x_2, 3);
lean_inc(x_255);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_256 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1(x_1, x_253, x_3, x_4, x_5, x_6, x_7, x_252);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
if (lean_obj_tag(x_257) == 0)
{
lean_dec(x_257);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_212 = x_256;
goto block_216;
}
else
{
lean_object* x_258; lean_object* x_259; 
lean_dec(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_259 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1(x_1, x_254, x_3, x_4, x_5, x_6, x_7, x_258);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
if (lean_obj_tag(x_260) == 0)
{
lean_dec(x_260);
lean_dec(x_255);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_212 = x_259;
goto block_216;
}
else
{
lean_object* x_261; lean_object* x_262; 
lean_dec(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1(x_1, x_255, x_3, x_4, x_5, x_6, x_7, x_261);
x_212 = x_262;
goto block_216;
}
}
else
{
lean_dec(x_255);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_212 = x_259;
goto block_216;
}
}
}
else
{
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_212 = x_256;
goto block_216;
}
}
case 10:
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_221, 1);
lean_inc(x_263);
lean_dec(x_221);
x_264 = lean_ctor_get(x_2, 1);
lean_inc(x_264);
x_265 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1(x_1, x_264, x_3, x_4, x_5, x_6, x_7, x_263);
x_212 = x_265;
goto block_216;
}
case 11:
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_221, 1);
lean_inc(x_266);
lean_dec(x_221);
x_267 = lean_ctor_get(x_2, 2);
lean_inc(x_267);
x_268 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1(x_1, x_267, x_3, x_4, x_5, x_6, x_7, x_266);
x_212 = x_268;
goto block_216;
}
default: 
{
lean_object* x_269; lean_object* x_270; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_269 = lean_ctor_get(x_221, 1);
lean_inc(x_269);
lean_dec(x_221);
x_270 = lean_box(0);
x_180 = x_270;
x_181 = x_269;
goto block_211;
}
}
}
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_271 = lean_ctor_get(x_221, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_221, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_273 = x_221;
} else {
 lean_dec_ref(x_221);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(1, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_271);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_275 = lean_ctor_get(x_220, 0);
lean_inc(x_275);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 x_276 = x_220;
} else {
 lean_dec_ref(x_220);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(1, 1, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_275);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_164);
return x_278;
}
block_211:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; size_t x_189; size_t x_190; size_t x_191; lean_object* x_192; uint8_t x_193; 
x_182 = lean_st_ref_take(x_3, x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_ctor_get(x_183, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_187 = x_183;
} else {
 lean_dec_ref(x_183);
 x_187 = lean_box(0);
}
x_188 = lean_array_get_size(x_186);
x_189 = lean_usize_of_nat(x_188);
lean_dec(x_188);
x_190 = lean_usize_sub(x_189, x_179);
x_191 = lean_usize_land(x_176, x_190);
x_192 = lean_array_uget(x_186, x_191);
x_193 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelMVars_visitExpr_spec__0___redArg(x_2, x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_194 = lean_nat_add(x_185, x_178);
lean_dec(x_185);
lean_inc(x_180);
x_195 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_195, 0, x_2);
lean_ctor_set(x_195, 1, x_180);
lean_ctor_set(x_195, 2, x_192);
x_196 = lean_array_uset(x_186, x_191, x_195);
x_197 = lean_unsigned_to_nat(2u);
x_198 = lean_nat_shiftl(x_194, x_197);
x_199 = lean_unsigned_to_nat(3u);
x_200 = lean_nat_div(x_198, x_199);
lean_dec(x_198);
x_201 = lean_array_get_size(x_196);
x_202 = lean_nat_dec_le(x_200, x_201);
lean_dec(x_201);
lean_dec(x_200);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelMVars_visitExpr_spec__1___redArg(x_196);
if (lean_is_scalar(x_187)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_187;
}
lean_ctor_set(x_204, 0, x_194);
lean_ctor_set(x_204, 1, x_203);
x_9 = x_180;
x_10 = x_184;
x_11 = x_204;
goto block_19;
}
else
{
lean_object* x_205; 
if (lean_is_scalar(x_187)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_187;
}
lean_ctor_set(x_205, 0, x_194);
lean_ctor_set(x_205, 1, x_196);
x_9 = x_180;
x_10 = x_184;
x_11 = x_205;
goto block_19;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_box(0);
x_207 = lean_array_uset(x_186, x_191, x_206);
lean_inc(x_180);
x_208 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_reduce_visit_spec__6___redArg(x_2, x_180, x_192);
x_209 = lean_array_uset(x_207, x_191, x_208);
if (lean_is_scalar(x_187)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_187;
}
lean_ctor_set(x_210, 0, x_185);
lean_ctor_set(x_210, 1, x_209);
x_9 = x_180;
x_10 = x_184;
x_11 = x_210;
goto block_19;
}
}
block_216:
{
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
if (lean_obj_tag(x_213) == 0)
{
lean_dec(x_213);
lean_dec(x_2);
return x_212;
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_ctor_get(x_213, 0);
lean_inc(x_215);
lean_dec(x_213);
x_180 = x_215;
x_181 = x_214;
goto block_211;
}
}
else
{
lean_dec(x_2);
return x_212;
}
}
}
block_19:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_st_ref_set(x_3, x_11, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_13; lean_object* x_31; 
x_31 = l_Lean_Meta_isMatcherAppCore_x3f(x_1, x_2);
if (lean_obj_tag(x_31) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = x_7;
goto block_12;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; lean_object* x_47; size_t x_48; lean_object* x_49; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = l_Lean_Expr_sort___override(x_33);
x_35 = l_Lean_Expr_getAppNumArgs(x_2);
lean_inc(x_35);
x_36 = lean_mk_array(x_35, x_34);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_sub(x_35, x_37);
lean_dec(x_35);
x_39 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_36, x_38);
x_40 = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(x_32);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_dec(x_32);
x_42 = lean_nat_add(x_40, x_41);
lean_dec(x_41);
x_43 = l_Array_toSubarray___redArg(x_39, x_40, x_42);
x_44 = lean_box(0);
x_45 = lean_ctor_get(x_43, 2);
lean_inc(x_45);
x_46 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
x_48 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_49 = l_Subarray_forInUnsafe_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__0(x_43, x_46, x_48, x_44, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_43);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_dec(x_50);
x_13 = x_49;
goto block_30;
}
else
{
lean_object* x_51; 
lean_dec(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_8 = x_51;
goto block_12;
}
}
else
{
x_13 = x_49;
goto block_30;
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
block_30:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_22 = x_14;
} else {
 lean_dec_ref(x_14);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 1, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_14);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_dec(x_13);
x_8 = x_25;
goto block_12;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_unsigned_to_nat(8u);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_shiftl(x_11, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_17 = l_Nat_nextPowerOfTwo(x_16);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = lean_mk_array(x_17, x_18);
lean_ctor_set(x_7, 1, x_19);
lean_ctor_set(x_7, 0, x_12);
x_20 = lean_st_mk_ref(x_7, x_10);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_9, 0);
lean_inc(x_23);
lean_dec(x_9);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch___lam__0___boxed), 7, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1(x_24, x_1, x_21, x_2, x_3, x_4, x_5, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_26);
lean_dec(x_21);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_box(1);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_box(1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_26);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec(x_25);
x_34 = lean_st_ref_get(x_21, x_33);
lean_dec(x_21);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_21);
x_41 = !lean_is_exclusive(x_25);
if (x_41 == 0)
{
return x_25;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_25, 0);
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_25);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_45 = lean_ctor_get(x_7, 0);
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_7);
x_47 = lean_unsigned_to_nat(8u);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_unsigned_to_nat(2u);
x_50 = lean_nat_shiftl(x_47, x_49);
x_51 = lean_unsigned_to_nat(3u);
x_52 = lean_nat_div(x_50, x_51);
lean_dec(x_50);
x_53 = l_Nat_nextPowerOfTwo(x_52);
lean_dec(x_52);
x_54 = lean_box(0);
x_55 = lean_mk_array(x_53, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_48);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_st_mk_ref(x_56, x_46);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_45, 0);
lean_inc(x_60);
lean_dec(x_45);
x_61 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch___lam__0___boxed), 7, 1);
lean_closure_set(x_61, 0, x_60);
x_62 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1(x_61, x_1, x_58, x_2, x_3, x_4, x_5, x_59);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_63);
lean_dec(x_58);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_box(1);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_63);
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
lean_dec(x_62);
x_69 = lean_st_ref_get(x_58, x_68);
lean_dec(x_58);
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
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_58);
x_74 = lean_ctor_get(x_62, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_62, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_76 = x_62;
} else {
 lean_dec_ref(x_62);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Subarray_forInUnsafe_loop___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1___lam__0(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_13 = l_Lean_Elab_Eqns_mkEqnTypes_go(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_2 = x_12;
x_8 = x_14;
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__1___redArg(x_1, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__2___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkEqnTypes_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_70 = lean_mk_string_unchecked("Elab", 4, 4);
x_71 = lean_mk_string_unchecked("definition", 10, 10);
x_72 = lean_mk_string_unchecked("eqns", 4, 4);
x_73 = l_Lean_Name_mkStr3(x_70, x_71, x_72);
lean_inc(x_73);
x_74 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__1___redArg(x_73, x_6, x_8);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_73);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
x_31 = x_7;
x_32 = x_77;
goto block_69;
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_74);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_79 = lean_ctor_get(x_74, 1);
x_80 = lean_ctor_get(x_74, 0);
lean_dec(x_80);
x_81 = lean_mk_string_unchecked("mkEqnTypes step\n", 16, 16);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
lean_inc(x_2);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_2);
lean_ctor_set_tag(x_74, 7);
lean_ctor_set(x_74, 1, x_83);
lean_ctor_set(x_74, 0, x_82);
x_84 = lean_mk_string_unchecked("", 0, 0);
x_85 = l_Lean_stringToMessageData(x_84);
lean_dec(x_84);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_74);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_addTrace___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__2___redArg(x_73, x_86, x_4, x_5, x_6, x_7, x_79);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
x_31 = x_7;
x_32 = x_88;
goto block_69;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_89 = lean_ctor_get(x_74, 1);
lean_inc(x_89);
lean_dec(x_74);
x_90 = lean_mk_string_unchecked("mkEqnTypes step\n", 16, 16);
x_91 = l_Lean_stringToMessageData(x_90);
lean_dec(x_90);
lean_inc(x_2);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_2);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_mk_string_unchecked("", 0, 0);
x_95 = l_Lean_stringToMessageData(x_94);
lean_dec(x_94);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_addTrace___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__2___redArg(x_73, x_96, x_4, x_5, x_6, x_7, x_89);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
x_31 = x_7;
x_32 = x_98;
goto block_69;
}
}
block_26:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_2);
x_15 = l_Lean_Elab_Eqns_splitMatch_x3f(x_2, x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_saveEqn(x_2, x_9, x_10, x_11, x_12, x_13, x_17);
lean_dec(x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_List_forM___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__0(x_1, x_20, x_9, x_10, x_11, x_12, x_13, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
block_69:
{
lean_object* x_33; 
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_2);
x_33 = l_Lean_Elab_Eqns_expandRHS_x3f(x_2, x_28, x_29, x_30, x_31, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_2);
x_36 = l_Lean_MVarId_getType_x27(x_2, x_28, x_29, x_30, x_31, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
x_39 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch(x_37, x_28, x_29, x_30, x_31, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_9 = x_27;
x_10 = x_28;
x_11 = x_29;
x_12 = x_30;
x_13 = x_31;
x_14 = x_42;
goto block_26;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_2);
x_44 = l_Lean_Elab_Eqns_simpMatch_x3f(x_2, x_28, x_29, x_30, x_31, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_9 = x_27;
x_10 = x_28;
x_11 = x_29;
x_12 = x_30;
x_13 = x_31;
x_14 = x_46;
goto block_26;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_2);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec(x_45);
x_2 = x_48;
x_3 = x_27;
x_4 = x_28;
x_5 = x_29;
x_6 = x_30;
x_7 = x_31;
x_8 = x_47;
goto _start;
}
}
else
{
uint8_t x_50; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_44);
if (x_50 == 0)
{
return x_44;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_44, 0);
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_44);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_39);
if (x_54 == 0)
{
return x_39;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get(x_39, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_39);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_36);
if (x_58 == 0)
{
return x_36;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_36, 0);
x_60 = lean_ctor_get(x_36, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_36);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_2);
x_62 = lean_ctor_get(x_33, 1);
lean_inc(x_62);
lean_dec(x_33);
x_63 = lean_ctor_get(x_34, 0);
lean_inc(x_63);
lean_dec(x_34);
x_2 = x_63;
x_3 = x_27;
x_4 = x_28;
x_5 = x_29;
x_6 = x_30;
x_7 = x_31;
x_8 = x_62;
goto _start;
}
}
else
{
uint8_t x_65; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_33);
if (x_65 == 0)
{
return x_33;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_33, 0);
x_67 = lean_ctor_get(x_33, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_33);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at___Lean_Elab_Eqns_mkEqnTypes_go_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkEqnTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = lean_st_mk_ref(x_9, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = l_Lean_Elab_Eqns_mkEqnTypes_go(x_1, x_2, x_11, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_11, x_14);
lean_dec(x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_11);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_st_ref_take(x_1, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_nat_add(x_13, x_7);
lean_inc(x_12);
lean_ctor_set(x_8, 1, x_14);
lean_ctor_set(x_8, 0, x_12);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_10, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 5);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 6);
lean_inc(x_20);
x_21 = lean_ctor_get(x_10, 7);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_8);
lean_ctor_set(x_22, 3, x_17);
lean_ctor_set(x_22, 4, x_18);
lean_ctor_set(x_22, 5, x_19);
lean_ctor_set(x_22, 6, x_20);
lean_ctor_set(x_22, 7, x_21);
x_23 = lean_st_ref_set(x_1, x_22, x_11);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = l_Lean_Name_num___override(x_12, x_13);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_Lean_Name_num___override(x_12, x_13);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_30 = lean_ctor_get(x_8, 0);
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_8);
x_32 = lean_ctor_get(x_6, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_dec(x_6);
x_34 = lean_nat_add(x_33, x_7);
lean_inc(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_30, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_30, 4);
lean_inc(x_39);
x_40 = lean_ctor_get(x_30, 5);
lean_inc(x_40);
x_41 = lean_ctor_get(x_30, 6);
lean_inc(x_41);
x_42 = lean_ctor_get(x_30, 7);
lean_inc(x_42);
lean_dec(x_30);
x_43 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_37);
lean_ctor_set(x_43, 2, x_35);
lean_ctor_set(x_43, 3, x_38);
lean_ctor_set(x_43, 4, x_39);
lean_ctor_set(x_43, 5, x_40);
lean_ctor_set(x_43, 6, x_41);
lean_ctor_set(x_43, 7, x_42);
x_44 = lean_st_ref_set(x_1, x_43, x_31);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = l_Lean_Name_num___override(x_32, x_33);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__0_spec__0___redArg(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__2___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_4, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_25; lean_object* x_26; 
x_16 = lean_array_uget(x_2, x_4);
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
x_25 = l_Lean_Expr_fvarId_x21(x_16);
x_26 = l_Lean_RBNode_findCore___at___Lean_Meta_removeUnused_spec__0___redArg(x_18, x_25);
lean_dec(x_25);
lean_dec(x_18);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_16);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_19);
x_7 = x_27;
x_8 = x_6;
goto block_13;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_26);
lean_inc(x_1);
x_28 = l_Lean_LocalContext_getFVar_x21(x_1, x_16);
x_29 = lean_ctor_get(x_28, 3);
lean_inc(x_29);
lean_dec(x_28);
x_20 = x_29;
goto block_24;
}
block_24:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_CollectFVars_main(x_20, x_17);
x_22 = lean_array_push(x_19, x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_7 = x_23;
x_8 = x_6;
goto block_13;
}
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
x_5 = x_7;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_removeUnusedEqnHypotheses_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 6)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 8);
lean_dec(x_4);
x_14 = l_Lean_mkFreshFVarId___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__0(x_7, x_8, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_expr_instantiate_rev(x_11, x_5);
lean_dec(x_11);
x_18 = l_Lean_Expr_bindingBody_x21(x_3);
lean_dec(x_3);
lean_inc(x_15);
x_19 = l_Lean_Expr_fvar___override(x_15);
x_20 = lean_array_push(x_5, x_19);
x_21 = lean_box(0);
x_22 = lean_unbox(x_21);
x_23 = l_Lean_LocalContext_mkLocalDecl(x_6, x_15, x_10, x_17, x_13, x_22);
x_3 = x_18;
x_4 = x_12;
x_5 = x_20;
x_6 = x_23;
x_9 = x_16;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; uint8_t x_47; 
x_25 = lean_expr_instantiate_rev(x_3, x_5);
lean_dec(x_3);
x_26 = lean_expr_instantiate_rev(x_4, x_5);
lean_dec(x_4);
x_27 = lean_unsigned_to_nat(8u);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_unsigned_to_nat(2u);
x_30 = lean_nat_shiftl(x_27, x_29);
x_31 = lean_unsigned_to_nat(3u);
x_32 = lean_nat_div(x_30, x_31);
lean_dec(x_30);
x_33 = l_Nat_nextPowerOfTwo(x_32);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = lean_mk_array(x_33, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_box(0);
x_38 = lean_mk_empty_array_with_capacity(x_28);
lean_inc(x_38);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_38);
lean_inc(x_25);
x_40 = l_Lean_CollectFVars_main(x_25, x_39);
lean_inc(x_26);
x_41 = l_Lean_CollectFVars_main(x_26, x_40);
lean_inc(x_5);
x_42 = l_Array_reverse(lean_box(0), x_5);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_38);
x_44 = lean_array_size(x_42);
x_45 = lean_usize_of_nat(x_28);
lean_inc(x_6);
x_46 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__2___redArg(x_6, x_42, x_44, x_45, x_43, x_9);
lean_dec(x_42);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_48, 1);
x_51 = lean_ctor_get(x_48, 0);
lean_dec(x_51);
x_52 = lean_array_get_size(x_50);
x_53 = lean_array_get_size(x_5);
lean_dec(x_5);
x_54 = lean_nat_dec_eq(x_52, x_53);
lean_dec(x_53);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_2);
lean_dec(x_1);
x_55 = l_Array_reverse(lean_box(0), x_50);
lean_inc(x_55);
lean_inc(x_6);
x_56 = l_Lean_LocalContext_mkForall(x_6, x_55, x_25);
lean_dec(x_25);
x_57 = l_Lean_LocalContext_mkLambda(x_6, x_55, x_26);
lean_dec(x_26);
lean_ctor_set(x_48, 1, x_57);
lean_ctor_set(x_48, 0, x_56);
return x_46;
}
else
{
lean_dec(x_50);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_6);
lean_ctor_set(x_48, 1, x_2);
lean_ctor_set(x_48, 0, x_1);
return x_46;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_dec(x_48);
x_59 = lean_array_get_size(x_58);
x_60 = lean_array_get_size(x_5);
lean_dec(x_5);
x_61 = lean_nat_dec_eq(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_2);
lean_dec(x_1);
x_62 = l_Array_reverse(lean_box(0), x_58);
lean_inc(x_62);
lean_inc(x_6);
x_63 = l_Lean_LocalContext_mkForall(x_6, x_62, x_25);
lean_dec(x_25);
x_64 = l_Lean_LocalContext_mkLambda(x_6, x_62, x_26);
lean_dec(x_26);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_46, 0, x_65);
return x_46;
}
else
{
lean_object* x_66; 
lean_dec(x_58);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_6);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_1);
lean_ctor_set(x_66, 1, x_2);
lean_ctor_set(x_46, 0, x_66);
return x_46;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_67 = lean_ctor_get(x_46, 0);
x_68 = lean_ctor_get(x_46, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_46);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
x_71 = lean_array_get_size(x_69);
x_72 = lean_array_get_size(x_5);
lean_dec(x_5);
x_73 = lean_nat_dec_eq(x_71, x_72);
lean_dec(x_72);
lean_dec(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_2);
lean_dec(x_1);
x_74 = l_Array_reverse(lean_box(0), x_69);
lean_inc(x_74);
lean_inc(x_6);
x_75 = l_Lean_LocalContext_mkForall(x_6, x_74, x_25);
lean_dec(x_25);
x_76 = l_Lean_LocalContext_mkLambda(x_6, x_74, x_26);
lean_dec(x_26);
if (lean_is_scalar(x_70)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_70;
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_68);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_69);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_6);
if (lean_is_scalar(x_70)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_70;
}
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_2);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_68);
return x_80;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkFreshFVarId___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__2___redArg(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Eqns_removeUnusedEqnHypotheses_go_spec__2(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_removeUnusedEqnHypotheses_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Eqns_removeUnusedEqnHypotheses_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_removeUnusedEqnHypotheses(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_mk_empty_array_with_capacity(x_6);
x_8 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_unsigned_to_nat(5u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_to_nat(x_12);
x_14 = lean_nat_pow(x_10, x_13);
lean_dec(x_13);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = lean_usize_to_nat(x_15);
x_17 = lean_mk_empty_array_with_capacity(x_16);
lean_dec(x_16);
lean_inc(x_17);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_6);
lean_ctor_set(x_19, 3, x_6);
lean_ctor_set_usize(x_19, 4, x_12);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Lean_Elab_Eqns_removeUnusedEqnHypotheses_go(x_1, x_2, x_1, x_2, x_7, x_21, x_3, x_4, x_5);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_removeUnusedEqnHypotheses___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Eqns_removeUnusedEqnHypotheses(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Eqns_deltaLHS___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_MVarId_getType_x27(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_mk_string_unchecked("Eq", 2, 2);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Lean_Expr_isAppOfArity(x_8, x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
x_14 = lean_mk_string_unchecked("deltaLHS", 8, 8);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_mk_string_unchecked("equality expected", 17, 17);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_MessageData_ofFormat(x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_Meta_throwTacticEx___redArg(x_15, x_1, x_19, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_box(x_13);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_deltaLHS___lam__0___boxed), 2, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = l_Lean_Expr_appFn_x21(x_8);
x_24 = l_Lean_Expr_appArg_x21(x_23);
lean_dec(x_23);
x_25 = l_Lean_Meta_delta_x3f(x_24, x_22, x_4, x_5, x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_8);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_mk_string_unchecked("deltaLHS", 8, 8);
x_29 = l_Lean_Name_mkStr1(x_28);
x_30 = lean_mk_string_unchecked("failed to delta reduce lhs", 26, 26);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_MessageData_ofFormat(x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_Meta_throwTacticEx___redArg(x_29, x_1, x_33, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_ctor_get(x_26, 0);
lean_inc(x_36);
lean_dec(x_26);
x_37 = l_Lean_Expr_appArg_x21(x_8);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_38 = l_Lean_Meta_mkEq(x_36, x_37, x_2, x_3, x_4, x_5, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_39, x_2, x_3, x_4, x_5, x_40);
lean_dec(x_2);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_25);
if (x_46 == 0)
{
return x_25;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_25, 0);
x_48 = lean_ctor_get(x_25, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_25);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_7);
if (x_50 == 0)
{
return x_7;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_7, 0);
x_52 = lean_ctor_get(x_7, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_7);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_deltaLHS___lam__1), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Elab_Eqns_deltaLHS___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Eqns_deltaLHS(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Eqns_deltaRHS_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaRHS_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_MVarId_getType_x27(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_mk_string_unchecked("Eq", 2, 2);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Expr_isAppOfArity(x_10, x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_free_object(x_8);
x_17 = l_Lean_Expr_appArg_x21(x_10);
x_18 = l_Lean_Expr_consumeMData(x_17);
lean_dec(x_17);
x_19 = l_Lean_Meta_delta_x3f(x_18, x_2, x_5, x_6, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = l_Lean_Expr_appFn_x21(x_10);
lean_dec(x_10);
x_31 = l_Lean_Expr_appArg_x21(x_30);
lean_dec(x_30);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_32 = l_Lean_Meta_mkEq(x_31, x_29, x_3, x_4, x_5, x_6, x_27);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_33, x_3, x_4, x_5, x_6, x_34);
lean_dec(x_3);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_ctor_set(x_20, 0, x_37);
lean_ctor_set(x_35, 0, x_20);
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
lean_ctor_set(x_20, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_20);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_free_object(x_20);
x_41 = !lean_is_exclusive(x_35);
if (x_41 == 0)
{
return x_35;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_35, 0);
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_35);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_free_object(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_32);
if (x_45 == 0)
{
return x_32;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_32, 0);
x_47 = lean_ctor_get(x_32, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_32);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_20, 0);
lean_inc(x_49);
lean_dec(x_20);
x_50 = l_Lean_Expr_appFn_x21(x_10);
lean_dec(x_10);
x_51 = l_Lean_Expr_appArg_x21(x_50);
lean_dec(x_50);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_52 = l_Lean_Meta_mkEq(x_51, x_49, x_3, x_4, x_5, x_6, x_27);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_53, x_3, x_4, x_5, x_6, x_54);
lean_dec(x_3);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_56);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_55, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_63 = x_55;
} else {
 lean_dec_ref(x_55);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_65 = lean_ctor_get(x_52, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_52, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_67 = x_52;
} else {
 lean_dec_ref(x_52);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_19);
if (x_69 == 0)
{
return x_19;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_19, 0);
x_71 = lean_ctor_get(x_19, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_19);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_73 = lean_ctor_get(x_8, 0);
x_74 = lean_ctor_get(x_8, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_8);
x_75 = lean_mk_string_unchecked("Eq", 2, 2);
x_76 = l_Lean_Name_mkStr1(x_75);
x_77 = lean_unsigned_to_nat(3u);
x_78 = l_Lean_Expr_isAppOfArity(x_73, x_76, x_77);
lean_dec(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_73);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_74);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = l_Lean_Expr_appArg_x21(x_73);
x_82 = l_Lean_Expr_consumeMData(x_81);
lean_dec(x_81);
x_83 = l_Lean_Meta_delta_x3f(x_82, x_2, x_5, x_6, x_74);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_73);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_dec(x_83);
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_91 = x_84;
} else {
 lean_dec_ref(x_84);
 x_91 = lean_box(0);
}
x_92 = l_Lean_Expr_appFn_x21(x_73);
lean_dec(x_73);
x_93 = l_Lean_Expr_appArg_x21(x_92);
lean_dec(x_92);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_94 = l_Lean_Meta_mkEq(x_93, x_90, x_3, x_4, x_5, x_6, x_89);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_95, x_3, x_4, x_5, x_6, x_96);
lean_dec(x_3);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_91;
}
lean_ctor_set(x_101, 0, x_98);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_91);
x_103 = lean_ctor_get(x_97, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_97, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_105 = x_97;
} else {
 lean_dec_ref(x_97);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_91);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_107 = lean_ctor_get(x_94, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_94, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_109 = x_94;
} else {
 lean_dec_ref(x_94);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_73);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_111 = lean_ctor_get(x_83, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_83, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_113 = x_83;
} else {
 lean_dec_ref(x_83);
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
else
{
uint8_t x_115; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_8);
if (x_115 == 0)
{
return x_8;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_8, 0);
x_117 = lean_ctor_get(x_8, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_8);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaRHS_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_deltaRHS_x3f___lam__0___boxed), 2, 1);
lean_closure_set(x_8, 0, x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_deltaRHS_x3f___lam__1), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaRHS_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Eqns_deltaRHS_x3f___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaRHS_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Eqns_deltaRHS_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_whnfAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Meta_whnfI(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_Expr_getAppFn(x_9);
if (lean_obj_tag(x_11) == 11)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_7);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
x_13 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_whnfAux(x_12, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
if (lean_obj_tag(x_11) == 11)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_11, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_11, 2);
lean_inc(x_30);
x_31 = lean_ptr_addr(x_30);
lean_dec(x_30);
x_32 = lean_ptr_addr(x_14);
x_33 = lean_usize_dec_eq(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_11);
x_34 = l_Lean_Expr_proj___override(x_28, x_29, x_14);
x_17 = x_34;
goto block_27;
}
else
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_14);
x_17 = x_11;
goto block_27;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_14);
lean_dec(x_11);
x_35 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_36 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateProj!Impl", 46, 46);
x_37 = lean_unsigned_to_nat(1813u);
x_38 = lean_unsigned_to_nat(18u);
x_39 = lean_mk_string_unchecked("proj expected", 13, 13);
x_40 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_35, x_36, x_37, x_38, x_39);
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_35);
x_41 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_40);
x_17 = x_41;
goto block_27;
}
block_27:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_box(0);
x_19 = l_Lean_Expr_sort___override(x_18);
x_20 = l_Lean_Expr_getAppNumArgs(x_9);
lean_inc(x_20);
x_21 = lean_mk_array(x_20, x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_20, x_22);
lean_dec(x_20);
x_24 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_9, x_21, x_23);
x_25 = l_Lean_mkAppN(x_17, x_24);
lean_dec(x_24);
if (lean_is_scalar(x_16)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_16;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_15);
return x_26;
}
}
else
{
lean_dec(x_11);
lean_dec(x_9);
return x_13;
}
}
else
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_7, 0);
x_43 = lean_ctor_get(x_7, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_7);
x_44 = l_Lean_Expr_getAppFn(x_42);
if (lean_obj_tag(x_44) == 11)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 2);
lean_inc(x_45);
x_46 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_whnfAux(x_45, x_2, x_3, x_4, x_5, x_43);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
if (lean_obj_tag(x_44) == 11)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_44, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_44, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_44, 2);
lean_inc(x_63);
x_64 = lean_ptr_addr(x_63);
lean_dec(x_63);
x_65 = lean_ptr_addr(x_47);
x_66 = lean_usize_dec_eq(x_64, x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_44);
x_67 = l_Lean_Expr_proj___override(x_61, x_62, x_47);
x_50 = x_67;
goto block_60;
}
else
{
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_47);
x_50 = x_44;
goto block_60;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_47);
lean_dec(x_44);
x_68 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_69 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateProj!Impl", 46, 46);
x_70 = lean_unsigned_to_nat(1813u);
x_71 = lean_unsigned_to_nat(18u);
x_72 = lean_mk_string_unchecked("proj expected", 13, 13);
x_73 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_68, x_69, x_70, x_71, x_72);
lean_dec(x_72);
lean_dec(x_69);
lean_dec(x_68);
x_74 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_73);
x_50 = x_74;
goto block_60;
}
block_60:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_box(0);
x_52 = l_Lean_Expr_sort___override(x_51);
x_53 = l_Lean_Expr_getAppNumArgs(x_42);
lean_inc(x_53);
x_54 = lean_mk_array(x_53, x_52);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_sub(x_53, x_55);
lean_dec(x_53);
x_57 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_42, x_54, x_56);
x_58 = l_Lean_mkAppN(x_50, x_57);
lean_dec(x_57);
if (lean_is_scalar(x_49)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_49;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_48);
return x_59;
}
}
else
{
lean_dec(x_44);
lean_dec(x_42);
return x_46;
}
}
else
{
lean_object* x_75; 
lean_dec(x_44);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_42);
lean_ctor_set(x_75, 1, x_43);
return x_75;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_whnfAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_whnfAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_MVarId_getType_x27(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_7);
x_16 = l_Lean_Expr_appFn_x21(x_9);
x_17 = l_Lean_Expr_appArg_x21(x_16);
lean_dec(x_16);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_17);
x_18 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_whnfAux(x_17, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_expr_eqv(x_20, x_17);
lean_dec(x_17);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_18);
x_23 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_24 = l_Lean_Meta_mkEq(x_20, x_23, x_2, x_3, x_4, x_5, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_25, x_2, x_3, x_4, x_5, x_26);
lean_dec(x_2);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
return x_24;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
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
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_box(0);
lean_ctor_set(x_18, 0, x_43);
return x_18;
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_18, 0);
x_45 = lean_ctor_get(x_18, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_18);
x_46 = lean_expr_eqv(x_44, x_17);
lean_dec(x_17);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_48 = l_Lean_Meta_mkEq(x_44, x_47, x_2, x_3, x_4, x_5, x_45);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_49, x_2, x_3, x_4, x_5, x_50);
lean_dec(x_2);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
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
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_52);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_59 = x_51;
} else {
 lean_dec_ref(x_51);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = lean_ctor_get(x_48, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_48, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_63 = x_48;
} else {
 lean_dec_ref(x_48);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_44);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_45);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_18);
if (x_67 == 0)
{
return x_18;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_18, 0);
x_69 = lean_ctor_get(x_18, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_18);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_71 = lean_ctor_get(x_7, 0);
x_72 = lean_ctor_get(x_7, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_7);
x_73 = lean_mk_string_unchecked("Eq", 2, 2);
x_74 = l_Lean_Name_mkStr1(x_73);
x_75 = lean_unsigned_to_nat(3u);
x_76 = l_Lean_Expr_isAppOfArity(x_71, x_74, x_75);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_71);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_72);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = l_Lean_Expr_appFn_x21(x_71);
x_80 = l_Lean_Expr_appArg_x21(x_79);
lean_dec(x_79);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_80);
x_81 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_whnfAux(x_80, x_2, x_3, x_4, x_5, x_72);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
x_85 = lean_expr_eqv(x_82, x_80);
lean_dec(x_80);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_84);
x_86 = l_Lean_Expr_appArg_x21(x_71);
lean_dec(x_71);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_87 = l_Lean_Meta_mkEq(x_82, x_86, x_2, x_3, x_4, x_5, x_83);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_88, x_2, x_3, x_4, x_5, x_89);
lean_dec(x_2);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
 x_93 = lean_box(0);
}
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_91);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_92);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_90, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_90, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_98 = x_90;
} else {
 lean_dec_ref(x_90);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = lean_ctor_get(x_87, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_87, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_102 = x_87;
} else {
 lean_dec_ref(x_87);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_82);
lean_dec(x_71);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = lean_box(0);
if (lean_is_scalar(x_84)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_84;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_83);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_80);
lean_dec(x_71);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = lean_ctor_get(x_81, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_81, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_108 = x_81;
} else {
 lean_dec_ref(x_81);
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
else
{
uint8_t x_110; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_7);
if (x_110 == 0)
{
return x_7;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_7, 0);
x_112 = lean_ctor_get(x_7, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_7);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryContradiction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_7 = lean_box(1);
x_8 = lean_unsigned_to_nat(16u);
x_9 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 1, x_11);
x_12 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 2, x_12);
x_13 = l_Lean_MVarId_contradictionCore(x_1, x_9, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryContradiction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Eqns_tryContradiction(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldThmType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_8);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_mk_string_unchecked("'", 1, 1);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_MessageData_ofConstName(x_1, x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked("' is not a definition", 21, 21);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_24, x_2, x_3, x_4, x_5, x_15);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_7);
if (x_26 == 0)
{
return x_7;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldThmType___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_const___override(x_1, x_2);
x_12 = l_Lean_mkAppN(x_11, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_Meta_mkEq(x_12, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(1);
x_17 = lean_box(1);
x_18 = lean_unbox(x_16);
x_19 = lean_unbox(x_17);
x_20 = l_Lean_Meta_mkForallFVars(x_4, x_14, x_3, x_18, x_19, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_20;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldThmType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_9 = l_Lean_Meta_getUnfoldEqnFor_x3f(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
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
lean_inc(x_1);
x_12 = l_Lean_getConstInfoDefn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldThmType_spec__0(x_1, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(x_16, x_17);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldThmType___lam__0___boxed), 10, 3);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_18);
lean_closure_set(x_19, 2, x_7);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
x_23 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_20, x_19, x_22, x_2, x_3, x_4, x_5, x_14);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_dec(x_9);
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
lean_dec(x_10);
x_30 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_29, x_2, x_3, x_4, x_5, x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = l_Lean_ConstantInfo_type(x_32);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_36 = l_Lean_ConstantInfo_type(x_34);
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
return x_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_30, 0);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_30);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_9);
if (x_42 == 0)
{
return x_9;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_9, 0);
x_44 = lean_ctor_get(x_9, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_9);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldThmType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfoDefn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldThmType_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldThmType___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldThmType___lam__0(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldLHS___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_9 = l_Lean_Meta_getUnfoldEqnFor_x3f(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Eqns_deltaLHS(x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l_Lean_MVarId_getType_x27(x_3, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_mk_string_unchecked("Eq", 2, 2);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = lean_unsigned_to_nat(3u);
x_21 = l_Lean_Expr_isAppOfArity(x_16, x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_1);
x_22 = lean_mk_string_unchecked("unfoldLHS: Unexpected target ", 29, 29);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = l_Lean_MessageData_ofExpr(x_16);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked("", 0, 0);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_28, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = l_Lean_Expr_appFn_x21(x_16);
x_31 = l_Lean_Expr_appArg_x21(x_30);
lean_dec(x_30);
x_32 = l_Lean_Expr_appArg_x21(x_16);
lean_dec(x_16);
x_33 = l_Lean_Expr_isAppOf(x_31, x_1);
lean_dec(x_1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_32);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_3);
x_34 = lean_mk_string_unchecked("unfoldLHS: Unexpected LHS ", 26, 26);
x_35 = l_Lean_stringToMessageData(x_34);
lean_dec(x_34);
x_36 = l_Lean_MessageData_ofExpr(x_31);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_mk_string_unchecked("", 0, 0);
x_39 = l_Lean_stringToMessageData(x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_40, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_46 = l_Lean_Expr_getAppFn(x_31);
x_47 = l_Lean_Expr_constLevels_x21(x_46);
lean_dec(x_46);
x_48 = l_Lean_Expr_const___override(x_14, x_47);
x_49 = lean_box(0);
x_50 = l_Lean_Expr_sort___override(x_49);
x_51 = l_Lean_Expr_getAppNumArgs(x_31);
lean_inc(x_51);
x_52 = lean_mk_array(x_51, x_50);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_sub(x_51, x_53);
lean_dec(x_51);
x_55 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_31, x_52, x_54);
x_56 = l_Lean_mkAppN(x_48, x_55);
lean_dec(x_55);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_56);
x_57 = lean_infer_type(x_56, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_Expr_isAppOfArity(x_58, x_19, x_20);
lean_dec(x_19);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_32);
lean_dec(x_3);
x_61 = lean_mk_string_unchecked("Lean.Elab.PreDefinition.Eqns", 28, 28);
x_62 = lean_mk_string_unchecked("_private.Lean.Elab.PreDefinition.Eqns.0.Lean.Elab.Eqns.unfoldLHS", 64, 64);
x_63 = lean_unsigned_to_nat(334u);
x_64 = lean_unsigned_to_nat(53u);
x_65 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_66 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_61, x_62, x_63, x_64, x_65);
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_61);
x_67 = l_panic___at___Lean_Meta_subst_substEq_spec__0(x_66, x_4, x_5, x_6, x_7, x_59);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = l_Lean_Expr_appArg_x21(x_58);
lean_dec(x_58);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_69 = l_Lean_Meta_mkEq(x_68, x_32, x_4, x_5, x_6, x_7, x_59);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_box(0);
lean_inc(x_4);
x_73 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_70, x_72, x_4, x_5, x_6, x_7, x_71);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_inc(x_5);
lean_inc(x_74);
x_76 = l_Lean_Meta_mkEqTrans(x_56, x_74, x_4, x_5, x_6, x_7, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_3, x_77, x_5, x_78);
lean_dec(x_5);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
x_82 = l_Lean_Expr_mvarId_x21(x_74);
lean_dec(x_74);
lean_ctor_set(x_79, 0, x_82);
return x_79;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = l_Lean_Expr_mvarId_x21(x_74);
lean_dec(x_74);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_dec(x_74);
lean_dec(x_5);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_76);
if (x_86 == 0)
{
return x_76;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_76, 0);
x_88 = lean_ctor_get(x_76, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_76);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_56);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_90 = !lean_is_exclusive(x_69);
if (x_90 == 0)
{
return x_69;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_69, 0);
x_92 = lean_ctor_get(x_69, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_69);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_56);
lean_dec(x_32);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_94 = !lean_is_exclusive(x_57);
if (x_94 == 0)
{
return x_57;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_57, 0);
x_96 = lean_ctor_get(x_57, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_57);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_15);
if (x_98 == 0)
{
return x_15;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_15, 0);
x_100 = lean_ctor_get(x_15, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_15);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_9);
if (x_102 == 0)
{
return x_9;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_9, 0);
x_104 = lean_ctor_get(x_9, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_9);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldLHS(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(0);
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldLHS___lam__0___boxed), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_2);
x_10 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_2, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldLHS___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldLHS___lam__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldLHS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldLHS(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof_go(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_2 = x_11;
x_7 = x_13;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof_go_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_13 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof_go(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
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
x_5 = x_14;
x_10 = x_15;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_13;
}
}
else
{
lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; 
x_322 = lean_mk_string_unchecked("Elab", 4, 4);
x_323 = lean_mk_string_unchecked("definition", 10, 10);
x_324 = lean_mk_string_unchecked("eqns", 4, 4);
x_325 = l_Lean_Name_mkStr3(x_322, x_323, x_324);
lean_inc(x_325);
x_326 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_325, x_3, x_4, x_5, x_6, x_7);
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_unbox(x_327);
lean_dec(x_327);
if (x_328 == 0)
{
lean_object* x_329; 
lean_dec(x_325);
x_329 = lean_ctor_get(x_326, 1);
lean_inc(x_329);
lean_dec(x_326);
x_310 = x_3;
x_311 = x_4;
x_312 = x_5;
x_313 = x_6;
x_314 = x_329;
goto block_321;
}
else
{
uint8_t x_330; 
x_330 = !lean_is_exclusive(x_326);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_331 = lean_ctor_get(x_326, 1);
x_332 = lean_ctor_get(x_326, 0);
lean_dec(x_332);
x_333 = lean_mk_string_unchecked("step\n", 5, 5);
x_334 = l_Lean_stringToMessageData(x_333);
lean_dec(x_333);
lean_inc(x_2);
x_335 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_335, 0, x_2);
lean_ctor_set_tag(x_326, 7);
lean_ctor_set(x_326, 1, x_335);
lean_ctor_set(x_326, 0, x_334);
x_336 = lean_mk_string_unchecked("", 0, 0);
x_337 = l_Lean_stringToMessageData(x_336);
lean_dec(x_336);
x_338 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_338, 0, x_326);
lean_ctor_set(x_338, 1, x_337);
x_339 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_325, x_338, x_3, x_4, x_5, x_6, x_331);
x_340 = lean_ctor_get(x_339, 1);
lean_inc(x_340);
lean_dec(x_339);
x_310 = x_3;
x_311 = x_4;
x_312 = x_5;
x_313 = x_6;
x_314 = x_340;
goto block_321;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_341 = lean_ctor_get(x_326, 1);
lean_inc(x_341);
lean_dec(x_326);
x_342 = lean_mk_string_unchecked("step\n", 5, 5);
x_343 = l_Lean_stringToMessageData(x_342);
lean_dec(x_342);
lean_inc(x_2);
x_344 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_344, 0, x_2);
x_345 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
x_346 = lean_mk_string_unchecked("", 0, 0);
x_347 = l_Lean_stringToMessageData(x_346);
lean_dec(x_346);
x_348 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_348, 0, x_345);
lean_ctor_set(x_348, 1, x_347);
x_349 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_325, x_348, x_3, x_4, x_5, x_6, x_341);
x_350 = lean_ctor_get(x_349, 1);
lean_inc(x_350);
lean_dec(x_349);
x_310 = x_3;
x_311 = x_4;
x_312 = x_5;
x_313 = x_6;
x_314 = x_350;
goto block_321;
}
}
block_309:
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; uint64_t x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_14, 0);
x_16 = lean_ctor_get_uint8(x_14, 1);
x_17 = lean_ctor_get_uint8(x_14, 2);
x_18 = lean_ctor_get_uint8(x_14, 3);
x_19 = lean_ctor_get_uint8(x_14, 4);
x_20 = lean_ctor_get_uint8(x_14, 5);
x_21 = lean_ctor_get_uint8(x_14, 6);
x_22 = lean_ctor_get_uint8(x_14, 7);
x_23 = lean_ctor_get_uint8(x_14, 8);
x_24 = lean_ctor_get_uint8(x_14, 10);
x_25 = lean_ctor_get_uint8(x_14, 11);
x_26 = lean_ctor_get_uint8(x_14, 12);
x_27 = lean_ctor_get_uint8(x_14, 13);
x_28 = lean_ctor_get_uint8(x_14, 14);
x_29 = lean_ctor_get_uint8(x_14, 15);
x_30 = lean_ctor_get_uint8(x_14, 16);
x_31 = lean_ctor_get_uint8(x_14, 17);
lean_dec(x_14);
x_32 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_32, 0, x_15);
lean_ctor_set_uint8(x_32, 1, x_16);
lean_ctor_set_uint8(x_32, 2, x_17);
lean_ctor_set_uint8(x_32, 3, x_18);
lean_ctor_set_uint8(x_32, 4, x_19);
lean_ctor_set_uint8(x_32, 5, x_20);
lean_ctor_set_uint8(x_32, 6, x_21);
lean_ctor_set_uint8(x_32, 7, x_22);
lean_ctor_set_uint8(x_32, 8, x_23);
lean_ctor_set_uint8(x_32, 9, x_13);
lean_ctor_set_uint8(x_32, 10, x_24);
lean_ctor_set_uint8(x_32, 11, x_25);
lean_ctor_set_uint8(x_32, 12, x_26);
lean_ctor_set_uint8(x_32, 13, x_27);
lean_ctor_set_uint8(x_32, 14, x_28);
lean_ctor_set_uint8(x_32, 15, x_29);
lean_ctor_set_uint8(x_32, 16, x_30);
lean_ctor_set_uint8(x_32, 17, x_31);
x_33 = lean_ctor_get_uint64(x_12, sizeof(void*)*7);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_uint64_of_nat(x_34);
x_36 = lean_uint64_shift_right(x_33, x_35);
x_37 = lean_uint64_shift_left(x_36, x_35);
x_38 = l_Lean_Meta_TransparencyMode_toUInt64(x_13);
x_39 = lean_uint64_lor(x_37, x_38);
x_40 = lean_ctor_get_uint8(x_12, sizeof(void*)*7 + 8);
x_41 = lean_ctor_get(x_12, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_12, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_12, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_12, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_12, 5);
lean_inc(x_45);
x_46 = lean_ctor_get(x_12, 6);
lean_inc(x_46);
x_47 = lean_ctor_get_uint8(x_12, sizeof(void*)*7 + 9);
x_48 = lean_ctor_get_uint8(x_12, sizeof(void*)*7 + 10);
x_49 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_49, 0, x_32);
lean_ctor_set(x_49, 1, x_41);
lean_ctor_set(x_49, 2, x_42);
lean_ctor_set(x_49, 3, x_43);
lean_ctor_set(x_49, 4, x_44);
lean_ctor_set(x_49, 5, x_45);
lean_ctor_set(x_49, 6, x_46);
lean_ctor_set_uint64(x_49, sizeof(void*)*7, x_39);
lean_ctor_set_uint8(x_49, sizeof(void*)*7 + 8, x_40);
lean_ctor_set_uint8(x_49, sizeof(void*)*7 + 9, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*7 + 10, x_48);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_11);
lean_inc(x_2);
x_50 = l_Lean_Elab_Eqns_tryURefl(x_2, x_49, x_11, x_8, x_10, x_9);
lean_dec(x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_11);
lean_inc(x_2);
x_54 = l_Lean_Elab_Eqns_tryContradiction(x_2, x_12, x_11, x_8, x_10, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_11);
lean_inc(x_2);
x_58 = l_Lean_Elab_Eqns_simpMatch_x3f(x_2, x_12, x_11, x_8, x_10, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_11);
lean_inc(x_12);
lean_inc(x_2);
x_61 = l_Lean_Elab_Eqns_simpIf_x3f(x_2, x_12, x_11, x_8, x_10, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_11);
lean_inc(x_2);
x_64 = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(x_2, x_12, x_11, x_8, x_10, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; uint8_t x_106; 
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_box(1);
x_68 = lean_unsigned_to_nat(100000u);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_34);
x_71 = lean_unbox(x_55);
lean_ctor_set_uint8(x_70, sizeof(void*)*2, x_71);
x_72 = lean_unbox(x_67);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 1, x_72);
x_73 = lean_unbox(x_55);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 2, x_73);
x_74 = lean_unbox(x_67);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 3, x_74);
x_75 = lean_unbox(x_67);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 4, x_75);
x_76 = lean_unbox(x_67);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 5, x_76);
x_77 = lean_unbox(x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 6, x_77);
x_78 = lean_unbox(x_67);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 7, x_78);
x_79 = lean_unbox(x_67);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 8, x_79);
x_80 = lean_unbox(x_55);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 9, x_80);
x_81 = lean_unbox(x_55);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 10, x_81);
x_82 = lean_unbox(x_55);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 11, x_82);
x_83 = lean_unbox(x_55);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 12, x_83);
x_84 = lean_unbox(x_67);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 13, x_84);
x_85 = lean_unbox(x_55);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 14, x_85);
x_86 = lean_unbox(x_55);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 15, x_86);
x_87 = lean_unbox(x_55);
lean_dec(x_55);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 16, x_87);
x_88 = lean_unbox(x_67);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 17, x_88);
x_89 = lean_unbox(x_67);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 18, x_89);
x_90 = lean_unbox(x_67);
lean_ctor_set_uint8(x_70, sizeof(void*)*2 + 19, x_90);
x_91 = l_Array_empty(lean_box(0));
x_92 = lean_unsigned_to_nat(8u);
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_nat_shiftl(x_92, x_34);
x_95 = lean_unsigned_to_nat(3u);
x_96 = lean_nat_div(x_94, x_95);
lean_dec(x_94);
x_97 = l_Nat_nextPowerOfTwo(x_96);
lean_dec(x_96);
x_98 = lean_box(0);
x_99 = lean_mk_array(x_97, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_93);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_101);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_unbox(x_67);
lean_ctor_set_uint8(x_103, sizeof(void*)*2, x_104);
lean_inc(x_91);
x_105 = l_Lean_Meta_Simp_mkContext(x_70, x_91, x_103, x_12, x_11, x_8, x_10, x_66);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; size_t x_113; lean_object* x_114; lean_object* x_115; size_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = lean_ctor_get(x_105, 1);
x_109 = lean_box(0);
lean_inc(x_101);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_101);
lean_inc(x_110);
lean_ctor_set(x_105, 1, x_93);
lean_ctor_set(x_105, 0, x_110);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_101);
x_112 = lean_unsigned_to_nat(5u);
x_113 = lean_usize_of_nat(x_112);
x_114 = lean_usize_to_nat(x_113);
x_115 = lean_nat_pow(x_34, x_114);
lean_dec(x_114);
x_116 = lean_usize_of_nat(x_115);
lean_dec(x_115);
x_117 = lean_usize_to_nat(x_116);
x_118 = lean_mk_empty_array_with_capacity(x_117);
lean_dec(x_117);
lean_inc(x_118);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
lean_ctor_set(x_120, 2, x_93);
lean_ctor_set(x_120, 3, x_93);
lean_ctor_set_usize(x_120, 4, x_113);
lean_inc(x_110);
x_121 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_121, 0, x_110);
lean_ctor_set(x_121, 1, x_110);
lean_ctor_set(x_121, 2, x_111);
lean_ctor_set(x_121, 3, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_105);
lean_ctor_set(x_122, 1, x_121);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_11);
lean_inc(x_2);
x_123 = l_Lean_Meta_simpTargetStar(x_2, x_107, x_91, x_109, x_122, x_12, x_11, x_8, x_10, x_108);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec(x_124);
switch (lean_obj_tag(x_125)) {
case 0:
{
uint8_t x_126; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_123);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_123, 0);
lean_dec(x_127);
x_128 = lean_box(0);
lean_ctor_set(x_123, 0, x_128);
return x_123;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_123, 1);
lean_inc(x_129);
lean_dec(x_123);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
case 1:
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_123, 1);
lean_inc(x_132);
lean_dec(x_123);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_11);
lean_inc(x_12);
lean_inc(x_2);
x_133 = l_Lean_Meta_casesOnStuckLHS_x3f(x_2, x_12, x_11, x_8, x_10, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; uint8_t x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_unbox(x_67);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_11);
lean_inc(x_12);
lean_inc(x_2);
x_137 = l_Lean_Meta_splitTarget_x3f(x_2, x_136, x_12, x_11, x_8, x_10, x_135);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_mk_string_unchecked("failed to generate equational theorem for '", 43, 43);
x_141 = l_Lean_stringToMessageData(x_140);
lean_dec(x_140);
x_142 = l_Lean_MessageData_ofName(x_1);
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_mk_string_unchecked("'\n", 2, 2);
x_145 = l_Lean_stringToMessageData(x_144);
lean_dec(x_144);
x_146 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_2);
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_mk_string_unchecked("", 0, 0);
x_150 = l_Lean_stringToMessageData(x_149);
lean_dec(x_149);
x_151 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_151, x_12, x_11, x_8, x_10, x_139);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_12);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_2);
x_153 = lean_ctor_get(x_137, 1);
lean_inc(x_153);
lean_dec(x_137);
x_154 = lean_ctor_get(x_138, 0);
lean_inc(x_154);
lean_dec(x_138);
x_155 = l_List_forM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof_go_spec__0(x_1, x_154, x_12, x_11, x_8, x_10, x_153);
return x_155;
}
}
else
{
uint8_t x_156; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_137);
if (x_156 == 0)
{
return x_137;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_137, 0);
x_158 = lean_ctor_get(x_137, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_137);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_2);
x_160 = !lean_is_exclusive(x_133);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_161 = lean_ctor_get(x_133, 1);
x_162 = lean_ctor_get(x_133, 0);
lean_dec(x_162);
x_163 = lean_ctor_get(x_134, 0);
lean_inc(x_163);
lean_dec(x_134);
x_164 = lean_array_get_size(x_163);
x_165 = lean_box(0);
x_166 = lean_nat_dec_lt(x_93, x_164);
if (x_166 == 0)
{
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_1);
lean_ctor_set(x_133, 0, x_165);
return x_133;
}
else
{
uint8_t x_167; 
x_167 = lean_nat_dec_le(x_164, x_164);
if (x_167 == 0)
{
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_1);
lean_ctor_set(x_133, 0, x_165);
return x_133;
}
else
{
size_t x_168; size_t x_169; lean_object* x_170; 
lean_free_object(x_133);
x_168 = lean_usize_of_nat(x_93);
x_169 = lean_usize_of_nat(x_164);
lean_dec(x_164);
x_170 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof_go_spec__1(x_1, x_163, x_168, x_169, x_165, x_12, x_11, x_8, x_10, x_161);
lean_dec(x_163);
return x_170;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_171 = lean_ctor_get(x_133, 1);
lean_inc(x_171);
lean_dec(x_133);
x_172 = lean_ctor_get(x_134, 0);
lean_inc(x_172);
lean_dec(x_134);
x_173 = lean_array_get_size(x_172);
x_174 = lean_box(0);
x_175 = lean_nat_dec_lt(x_93, x_173);
if (x_175 == 0)
{
lean_object* x_176; 
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_1);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_171);
return x_176;
}
else
{
uint8_t x_177; 
x_177 = lean_nat_dec_le(x_173, x_173);
if (x_177 == 0)
{
lean_object* x_178; 
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_1);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_171);
return x_178;
}
else
{
size_t x_179; size_t x_180; lean_object* x_181; 
x_179 = lean_usize_of_nat(x_93);
x_180 = lean_usize_of_nat(x_173);
lean_dec(x_173);
x_181 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof_go_spec__1(x_1, x_172, x_179, x_180, x_174, x_12, x_11, x_8, x_10, x_171);
lean_dec(x_172);
return x_181;
}
}
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_133);
if (x_182 == 0)
{
return x_133;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_133, 0);
x_184 = lean_ctor_get(x_133, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_133);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
default: 
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_2);
x_186 = lean_ctor_get(x_123, 1);
lean_inc(x_186);
lean_dec(x_123);
x_187 = lean_ctor_get(x_125, 0);
lean_inc(x_187);
lean_dec(x_125);
x_2 = x_187;
x_3 = x_12;
x_4 = x_11;
x_5 = x_8;
x_6 = x_10;
x_7 = x_186;
goto _start;
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_123);
if (x_189 == 0)
{
return x_123;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_123, 0);
x_191 = lean_ctor_get(x_123, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_123);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; size_t x_200; lean_object* x_201; lean_object* x_202; size_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_193 = lean_ctor_get(x_105, 0);
x_194 = lean_ctor_get(x_105, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_105);
x_195 = lean_box(0);
lean_inc(x_101);
x_196 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_196, 0, x_101);
lean_inc(x_196);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_93);
x_198 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_198, 0, x_101);
x_199 = lean_unsigned_to_nat(5u);
x_200 = lean_usize_of_nat(x_199);
x_201 = lean_usize_to_nat(x_200);
x_202 = lean_nat_pow(x_34, x_201);
lean_dec(x_201);
x_203 = lean_usize_of_nat(x_202);
lean_dec(x_202);
x_204 = lean_usize_to_nat(x_203);
x_205 = lean_mk_empty_array_with_capacity(x_204);
lean_dec(x_204);
lean_inc(x_205);
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_205);
x_207 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_205);
lean_ctor_set(x_207, 2, x_93);
lean_ctor_set(x_207, 3, x_93);
lean_ctor_set_usize(x_207, 4, x_200);
lean_inc(x_196);
x_208 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_208, 0, x_196);
lean_ctor_set(x_208, 1, x_196);
lean_ctor_set(x_208, 2, x_198);
lean_ctor_set(x_208, 3, x_207);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_197);
lean_ctor_set(x_209, 1, x_208);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_11);
lean_inc(x_2);
x_210 = l_Lean_Meta_simpTargetStar(x_2, x_193, x_91, x_195, x_209, x_12, x_11, x_8, x_10, x_194);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
lean_dec(x_211);
switch (lean_obj_tag(x_212)) {
case 0:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_214 = x_210;
} else {
 lean_dec_ref(x_210);
 x_214 = lean_box(0);
}
x_215 = lean_box(0);
if (lean_is_scalar(x_214)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_214;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_213);
return x_216;
}
case 1:
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_210, 1);
lean_inc(x_217);
lean_dec(x_210);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_11);
lean_inc(x_12);
lean_inc(x_2);
x_218 = l_Lean_Meta_casesOnStuckLHS_x3f(x_2, x_12, x_11, x_8, x_10, x_217);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; uint8_t x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = lean_unbox(x_67);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_11);
lean_inc(x_12);
lean_inc(x_2);
x_222 = l_Lean_Meta_splitTarget_x3f(x_2, x_221, x_12, x_11, x_8, x_10, x_220);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_mk_string_unchecked("failed to generate equational theorem for '", 43, 43);
x_226 = l_Lean_stringToMessageData(x_225);
lean_dec(x_225);
x_227 = l_Lean_MessageData_ofName(x_1);
x_228 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_mk_string_unchecked("'\n", 2, 2);
x_230 = l_Lean_stringToMessageData(x_229);
lean_dec(x_229);
x_231 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_230);
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_2);
x_233 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
x_234 = lean_mk_string_unchecked("", 0, 0);
x_235 = l_Lean_stringToMessageData(x_234);
lean_dec(x_234);
x_236 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_235);
x_237 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_236, x_12, x_11, x_8, x_10, x_224);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_12);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_2);
x_238 = lean_ctor_get(x_222, 1);
lean_inc(x_238);
lean_dec(x_222);
x_239 = lean_ctor_get(x_223, 0);
lean_inc(x_239);
lean_dec(x_223);
x_240 = l_List_forM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof_go_spec__0(x_1, x_239, x_12, x_11, x_8, x_10, x_238);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_241 = lean_ctor_get(x_222, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_222, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_243 = x_222;
} else {
 lean_dec_ref(x_222);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_242);
return x_244;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
lean_dec(x_2);
x_245 = lean_ctor_get(x_218, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_246 = x_218;
} else {
 lean_dec_ref(x_218);
 x_246 = lean_box(0);
}
x_247 = lean_ctor_get(x_219, 0);
lean_inc(x_247);
lean_dec(x_219);
x_248 = lean_array_get_size(x_247);
x_249 = lean_box(0);
x_250 = lean_nat_dec_lt(x_93, x_248);
if (x_250 == 0)
{
lean_object* x_251; 
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_1);
if (lean_is_scalar(x_246)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_246;
}
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_245);
return x_251;
}
else
{
uint8_t x_252; 
x_252 = lean_nat_dec_le(x_248, x_248);
if (x_252 == 0)
{
lean_object* x_253; 
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_1);
if (lean_is_scalar(x_246)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_246;
}
lean_ctor_set(x_253, 0, x_249);
lean_ctor_set(x_253, 1, x_245);
return x_253;
}
else
{
size_t x_254; size_t x_255; lean_object* x_256; 
lean_dec(x_246);
x_254 = lean_usize_of_nat(x_93);
x_255 = lean_usize_of_nat(x_248);
lean_dec(x_248);
x_256 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof_go_spec__1(x_1, x_247, x_254, x_255, x_249, x_12, x_11, x_8, x_10, x_245);
lean_dec(x_247);
return x_256;
}
}
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_257 = lean_ctor_get(x_218, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_218, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_259 = x_218;
} else {
 lean_dec_ref(x_218);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
default: 
{
lean_object* x_261; lean_object* x_262; 
lean_dec(x_2);
x_261 = lean_ctor_get(x_210, 1);
lean_inc(x_261);
lean_dec(x_210);
x_262 = lean_ctor_get(x_212, 0);
lean_inc(x_262);
lean_dec(x_212);
x_2 = x_262;
x_3 = x_12;
x_4 = x_11;
x_5 = x_8;
x_6 = x_10;
x_7 = x_261;
goto _start;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_264 = lean_ctor_get(x_210, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_210, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_266 = x_210;
} else {
 lean_dec_ref(x_210);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
}
else
{
lean_object* x_268; lean_object* x_269; 
lean_dec(x_55);
lean_dec(x_2);
x_268 = lean_ctor_get(x_64, 1);
lean_inc(x_268);
lean_dec(x_64);
x_269 = lean_ctor_get(x_65, 0);
lean_inc(x_269);
lean_dec(x_65);
x_2 = x_269;
x_3 = x_12;
x_4 = x_11;
x_5 = x_8;
x_6 = x_10;
x_7 = x_268;
goto _start;
}
}
else
{
uint8_t x_271; 
lean_dec(x_55);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_271 = !lean_is_exclusive(x_64);
if (x_271 == 0)
{
return x_64;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_64, 0);
x_273 = lean_ctor_get(x_64, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_64);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
}
else
{
lean_object* x_275; lean_object* x_276; 
lean_dec(x_55);
lean_dec(x_2);
x_275 = lean_ctor_get(x_61, 1);
lean_inc(x_275);
lean_dec(x_61);
x_276 = lean_ctor_get(x_62, 0);
lean_inc(x_276);
lean_dec(x_62);
x_2 = x_276;
x_3 = x_12;
x_4 = x_11;
x_5 = x_8;
x_6 = x_10;
x_7 = x_275;
goto _start;
}
}
else
{
uint8_t x_278; 
lean_dec(x_55);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_278 = !lean_is_exclusive(x_61);
if (x_278 == 0)
{
return x_61;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_61, 0);
x_280 = lean_ctor_get(x_61, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_61);
x_281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
return x_281;
}
}
}
else
{
lean_object* x_282; lean_object* x_283; 
lean_dec(x_55);
lean_dec(x_2);
x_282 = lean_ctor_get(x_58, 1);
lean_inc(x_282);
lean_dec(x_58);
x_283 = lean_ctor_get(x_59, 0);
lean_inc(x_283);
lean_dec(x_59);
x_2 = x_283;
x_3 = x_12;
x_4 = x_11;
x_5 = x_8;
x_6 = x_10;
x_7 = x_282;
goto _start;
}
}
else
{
uint8_t x_285; 
lean_dec(x_55);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_285 = !lean_is_exclusive(x_58);
if (x_285 == 0)
{
return x_58;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_58, 0);
x_287 = lean_ctor_get(x_58, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_58);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
return x_288;
}
}
}
else
{
uint8_t x_289; 
lean_dec(x_55);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_289 = !lean_is_exclusive(x_54);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_54, 0);
lean_dec(x_290);
x_291 = lean_box(0);
lean_ctor_set(x_54, 0, x_291);
return x_54;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_54, 1);
lean_inc(x_292);
lean_dec(x_54);
x_293 = lean_box(0);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
}
}
else
{
uint8_t x_295; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_295 = !lean_is_exclusive(x_54);
if (x_295 == 0)
{
return x_54;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_54, 0);
x_297 = lean_ctor_get(x_54, 1);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_54);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
return x_298;
}
}
}
else
{
uint8_t x_299; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_299 = !lean_is_exclusive(x_50);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_ctor_get(x_50, 0);
lean_dec(x_300);
x_301 = lean_box(0);
lean_ctor_set(x_50, 0, x_301);
return x_50;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_50, 1);
lean_inc(x_302);
lean_dec(x_50);
x_303 = lean_box(0);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_302);
return x_304;
}
}
}
else
{
uint8_t x_305; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_305 = !lean_is_exclusive(x_50);
if (x_305 == 0)
{
return x_50;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_50, 0);
x_307 = lean_ctor_get(x_50, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_50);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
block_321:
{
lean_object* x_315; lean_object* x_316; uint8_t x_317; uint8_t x_318; uint8_t x_319; 
x_315 = lean_box(0);
x_316 = lean_ctor_get(x_310, 0);
lean_inc(x_316);
x_317 = lean_ctor_get_uint8(x_316, 9);
lean_dec(x_316);
x_318 = lean_unbox(x_315);
x_319 = l_Lean_Meta_TransparencyMode_lt(x_317, x_318);
if (x_319 == 0)
{
x_8 = x_312;
x_9 = x_314;
x_10 = x_313;
x_11 = x_311;
x_12 = x_310;
x_13 = x_317;
goto block_309;
}
else
{
uint8_t x_320; 
x_320 = lean_unbox(x_315);
x_8 = x_312;
x_9 = x_314;
x_10 = x_313;
x_11 = x_311;
x_12 = x_310;
x_13 = x_320;
goto block_309;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof_go_spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_5);
x_10 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_mvarId_x21(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l_Lean_MVarId_intros(x_13, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_38; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
if (x_4 == 0)
{
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
x_22 = x_16;
goto block_37;
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; 
x_86 = lean_box(0);
x_87 = lean_ctor_get(x_5, 0);
lean_inc(x_87);
x_88 = lean_ctor_get_uint8(x_87, 9);
lean_dec(x_87);
x_89 = lean_unbox(x_86);
x_90 = l_Lean_Meta_TransparencyMode_lt(x_88, x_89);
if (x_90 == 0)
{
x_38 = x_88;
goto block_85;
}
else
{
uint8_t x_91; 
x_91 = lean_unbox(x_86);
x_38 = x_91;
goto block_85;
}
}
block_37:
{
lean_object* x_23; 
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_3);
x_23 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldLHS(x_3, x_17, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_19);
x_26 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof_go(x_3, x_24, x_18, x_19, x_20, x_21, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_11, x_19, x_27);
lean_dec(x_19);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_19);
lean_dec(x_11);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
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
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
block_85:
{
lean_object* x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; uint64_t x_58; lean_object* x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; 
x_39 = lean_ctor_get(x_5, 0);
lean_inc(x_39);
x_40 = lean_ctor_get_uint8(x_39, 0);
x_41 = lean_ctor_get_uint8(x_39, 1);
x_42 = lean_ctor_get_uint8(x_39, 2);
x_43 = lean_ctor_get_uint8(x_39, 3);
x_44 = lean_ctor_get_uint8(x_39, 4);
x_45 = lean_ctor_get_uint8(x_39, 5);
x_46 = lean_ctor_get_uint8(x_39, 6);
x_47 = lean_ctor_get_uint8(x_39, 7);
x_48 = lean_ctor_get_uint8(x_39, 8);
x_49 = lean_ctor_get_uint8(x_39, 10);
x_50 = lean_ctor_get_uint8(x_39, 11);
x_51 = lean_ctor_get_uint8(x_39, 12);
x_52 = lean_ctor_get_uint8(x_39, 13);
x_53 = lean_ctor_get_uint8(x_39, 14);
x_54 = lean_ctor_get_uint8(x_39, 15);
x_55 = lean_ctor_get_uint8(x_39, 16);
x_56 = lean_ctor_get_uint8(x_39, 17);
lean_dec(x_39);
x_57 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_57, 0, x_40);
lean_ctor_set_uint8(x_57, 1, x_41);
lean_ctor_set_uint8(x_57, 2, x_42);
lean_ctor_set_uint8(x_57, 3, x_43);
lean_ctor_set_uint8(x_57, 4, x_44);
lean_ctor_set_uint8(x_57, 5, x_45);
lean_ctor_set_uint8(x_57, 6, x_46);
lean_ctor_set_uint8(x_57, 7, x_47);
lean_ctor_set_uint8(x_57, 8, x_48);
lean_ctor_set_uint8(x_57, 9, x_38);
lean_ctor_set_uint8(x_57, 10, x_49);
lean_ctor_set_uint8(x_57, 11, x_50);
lean_ctor_set_uint8(x_57, 12, x_51);
lean_ctor_set_uint8(x_57, 13, x_52);
lean_ctor_set_uint8(x_57, 14, x_53);
lean_ctor_set_uint8(x_57, 15, x_54);
lean_ctor_set_uint8(x_57, 16, x_55);
lean_ctor_set_uint8(x_57, 17, x_56);
x_58 = lean_ctor_get_uint64(x_5, sizeof(void*)*7);
x_59 = lean_unsigned_to_nat(2u);
x_60 = lean_uint64_of_nat(x_59);
x_61 = lean_uint64_shift_right(x_58, x_60);
x_62 = lean_uint64_shift_left(x_61, x_60);
x_63 = l_Lean_Meta_TransparencyMode_toUInt64(x_38);
x_64 = lean_uint64_lor(x_62, x_63);
x_65 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 8);
x_66 = lean_ctor_get(x_5, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_5, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_5, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_5, 4);
lean_inc(x_69);
x_70 = lean_ctor_get(x_5, 5);
lean_inc(x_70);
x_71 = lean_ctor_get(x_5, 6);
lean_inc(x_71);
x_72 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_73 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
x_74 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_74, 0, x_57);
lean_ctor_set(x_74, 1, x_66);
lean_ctor_set(x_74, 2, x_67);
lean_ctor_set(x_74, 3, x_68);
lean_ctor_set(x_74, 4, x_69);
lean_ctor_set(x_74, 5, x_70);
lean_ctor_set(x_74, 6, x_71);
lean_ctor_set_uint64(x_74, sizeof(void*)*7, x_64);
lean_ctor_set_uint8(x_74, sizeof(void*)*7 + 8, x_65);
lean_ctor_set_uint8(x_74, sizeof(void*)*7 + 9, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*7 + 10, x_73);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_17);
x_75 = l_Lean_Elab_Eqns_tryURefl(x_17, x_74, x_6, x_7, x_8, x_16);
lean_dec(x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
x_22 = x_78;
goto block_37;
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
x_80 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_11, x_6, x_79);
lean_dec(x_6);
return x_80;
}
}
else
{
uint8_t x_81; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_75);
if (x_81 == 0)
{
return x_75;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_75, 0);
x_83 = lean_ctor_get(x_75, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_75);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_92 = !lean_is_exclusive(x_14);
if (x_92 == 0)
{
return x_14;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_14, 0);
x_94 = lean_ctor_get(x_14, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_14);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_mk_string_unchecked("Elab", 4, 4);
x_22 = lean_mk_string_unchecked("definition", 10, 10);
x_23 = lean_mk_string_unchecked("eqns", 4, 4);
x_24 = l_Lean_Name_mkStr3(x_21, x_22, x_23);
lean_inc(x_24);
x_25 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_24, x_4, x_5, x_6, x_7, x_8);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_28;
goto block_20;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_25, 1);
x_31 = lean_ctor_get(x_25, 0);
lean_dec(x_31);
x_32 = lean_mk_string_unchecked("proving: ", 9, 9);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
lean_inc(x_2);
x_34 = l_Lean_MessageData_ofExpr(x_2);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_34);
lean_ctor_set(x_25, 0, x_33);
x_35 = lean_mk_string_unchecked("", 0, 0);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_24, x_37, x_4, x_5, x_6, x_7, x_30);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_39;
goto block_20;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_dec(x_25);
x_41 = lean_mk_string_unchecked("proving: ", 9, 9);
x_42 = l_Lean_stringToMessageData(x_41);
lean_dec(x_41);
lean_inc(x_2);
x_43 = l_Lean_MessageData_ofExpr(x_2);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_mk_string_unchecked("", 0, 0);
x_46 = l_Lean_stringToMessageData(x_45);
lean_dec(x_45);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_24, x_47, x_4, x_5, x_6, x_7, x_40);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_49;
goto block_20;
}
}
block_20:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_box(0);
x_15 = lean_box(x_3);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof___lam__0___boxed), 9, 4);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_1);
lean_closure_set(x_16, 3, x_15);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_16, x_18, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof___lam__0(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkEqns_doRealize(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_104; uint8_t x_105; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_8, 2);
lean_inc(x_14);
x_15 = l_Lean_Meta_tactic_hygienic;
x_16 = lean_box(0);
x_17 = l_Lean_diagnostics;
x_18 = lean_unbox(x_16);
x_19 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_14, x_15, x_18);
x_20 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_19, x_17);
x_104 = lean_ctor_get(x_12, 0);
lean_inc(x_104);
lean_dec(x_12);
x_105 = l_Lean_Kernel_isDiagnosticsEnabled(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
if (x_20 == 0)
{
x_21 = x_8;
x_22 = x_9;
x_23 = x_13;
goto block_69;
}
else
{
goto block_103;
}
}
else
{
if (x_20 == 0)
{
goto block_103;
}
else
{
x_21 = x_8;
x_22 = x_9;
x_23 = x_13;
goto block_69;
}
}
block_69:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 3);
lean_inc(x_26);
x_27 = l_Lean_maxRecDepth;
x_28 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_19, x_27);
x_29 = lean_ctor_get(x_21, 5);
lean_inc(x_29);
x_30 = lean_ctor_get(x_21, 6);
lean_inc(x_30);
x_31 = lean_ctor_get(x_21, 7);
lean_inc(x_31);
x_32 = lean_ctor_get(x_21, 8);
lean_inc(x_32);
x_33 = lean_ctor_get(x_21, 9);
lean_inc(x_33);
x_34 = lean_ctor_get(x_21, 10);
lean_inc(x_34);
x_35 = lean_ctor_get(x_21, 11);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_21, sizeof(void*)*13 + 1);
x_37 = lean_ctor_get(x_21, 12);
lean_inc(x_37);
lean_dec(x_21);
x_38 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_25);
lean_ctor_set(x_38, 2, x_19);
lean_ctor_set(x_38, 3, x_26);
lean_ctor_set(x_38, 4, x_28);
lean_ctor_set(x_38, 5, x_29);
lean_ctor_set(x_38, 6, x_30);
lean_ctor_set(x_38, 7, x_31);
lean_ctor_set(x_38, 8, x_32);
lean_ctor_set(x_38, 9, x_33);
lean_ctor_set(x_38, 10, x_34);
lean_ctor_set(x_38, 11, x_35);
lean_ctor_set(x_38, 12, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*13, x_20);
lean_ctor_set_uint8(x_38, sizeof(void*)*13 + 1, x_36);
lean_inc(x_22);
lean_inc(x_38);
lean_inc(x_5);
x_39 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof(x_1, x_5, x_2, x_6, x_7, x_38, x_22, x_23);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Elab_Eqns_removeUnusedEqnHypotheses(x_5, x_40, x_38, x_22, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_43, 0);
x_47 = lean_ctor_get(x_43, 1);
x_48 = lean_ctor_get(x_4, 0);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_inc(x_3);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_3);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_46);
x_51 = lean_box(0);
lean_ctor_set_tag(x_43, 1);
lean_ctor_set(x_43, 1, x_51);
lean_ctor_set(x_43, 0, x_3);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_47);
lean_ctor_set(x_52, 2, x_43);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_addDecl(x_53, x_38, x_22, x_44);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_55 = lean_ctor_get(x_43, 0);
x_56 = lean_ctor_get(x_43, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_43);
x_57 = lean_ctor_get(x_4, 0);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_inc(x_3);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_3);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_55);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_3);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_56);
lean_ctor_set(x_62, 2, x_61);
x_63 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = l_Lean_addDecl(x_63, x_38, x_22, x_44);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_38);
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_39);
if (x_65 == 0)
{
return x_39;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_39, 0);
x_67 = lean_ctor_get(x_39, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_39);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
block_103:
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_st_ref_take(x_9, x_13);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_ctor_get(x_70, 1);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = l_Lean_Kernel_enableDiag(x_74, x_20);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_72, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_72, 3);
lean_inc(x_78);
x_79 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_79);
lean_inc(x_80);
lean_ctor_set(x_70, 1, x_80);
lean_ctor_set(x_70, 0, x_80);
x_81 = lean_ctor_get(x_72, 5);
lean_inc(x_81);
x_82 = lean_ctor_get(x_72, 6);
lean_inc(x_82);
x_83 = lean_ctor_get(x_72, 7);
lean_inc(x_83);
lean_dec(x_72);
x_84 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_84, 0, x_75);
lean_ctor_set(x_84, 1, x_76);
lean_ctor_set(x_84, 2, x_77);
lean_ctor_set(x_84, 3, x_78);
lean_ctor_set(x_84, 4, x_70);
lean_ctor_set(x_84, 5, x_81);
lean_ctor_set(x_84, 6, x_82);
lean_ctor_set(x_84, 7, x_83);
x_85 = lean_st_ref_set(x_9, x_84, x_73);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_21 = x_8;
x_22 = x_9;
x_23 = x_86;
goto block_69;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_87 = lean_ctor_get(x_70, 0);
x_88 = lean_ctor_get(x_70, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_70);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
x_90 = l_Lean_Kernel_enableDiag(x_89, x_20);
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_87, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_87, 3);
lean_inc(x_93);
x_94 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
lean_inc(x_95);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_ctor_get(x_87, 5);
lean_inc(x_97);
x_98 = lean_ctor_get(x_87, 6);
lean_inc(x_98);
x_99 = lean_ctor_get(x_87, 7);
lean_inc(x_99);
lean_dec(x_87);
x_100 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_100, 0, x_90);
lean_ctor_set(x_100, 1, x_91);
lean_ctor_set(x_100, 2, x_92);
lean_ctor_set(x_100, 3, x_93);
lean_ctor_set(x_100, 4, x_96);
lean_ctor_set(x_100, 5, x_97);
lean_ctor_set(x_100, 6, x_98);
lean_ctor_set(x_100, 7, x_99);
x_101 = lean_st_ref_set(x_9, x_100, x_88);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_21 = x_8;
x_22 = x_9;
x_23 = x_102;
goto block_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkEqns_doRealize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Elab_Eqns_mkEqns_doRealize(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Eqns_mkEqns_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_nat_dec_lt(x_7, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_mk_string_unchecked("Elab", 4, 4);
x_17 = lean_mk_string_unchecked("definition", 10, 10);
x_18 = lean_mk_string_unchecked("eqns", 4, 4);
x_19 = l_Lean_Name_mkStr3(x_16, x_17, x_18);
lean_inc(x_19);
x_20 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_19, x_8, x_9, x_10, x_11, x_12);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_49; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_array_fget(x_1, x_7);
x_49 = lean_unbox(x_22);
lean_dec(x_22);
if (x_49 == 0)
{
lean_free_object(x_20);
lean_dec(x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_26 = x_6;
x_27 = x_8;
x_28 = x_9;
x_29 = x_10;
x_30 = x_11;
x_31 = x_23;
goto block_48;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_50 = lean_mk_string_unchecked("eqnType[", 8, 8);
x_51 = l_Lean_stringToMessageData(x_50);
lean_dec(x_50);
lean_inc(x_7);
x_52 = l___private_Init_Data_Repr_0__Nat_reprFast(x_7);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_MessageData_ofFormat(x_53);
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_54);
lean_ctor_set(x_20, 0, x_51);
x_55 = lean_mk_string_unchecked("]: ", 3, 3);
x_56 = l_Lean_stringToMessageData(x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_20);
lean_ctor_set(x_57, 1, x_56);
lean_inc(x_25);
x_58 = l_Lean_MessageData_ofExpr(x_25);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_mk_string_unchecked("", 0, 0);
x_61 = l_Lean_stringToMessageData(x_60);
lean_dec(x_60);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_19, x_62, x_8, x_9, x_10, x_11, x_23);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_26 = x_6;
x_27 = x_8;
x_28 = x_9;
x_29 = x_10;
x_30 = x_11;
x_31 = x_64;
goto block_48;
}
block_48:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_mk_string_unchecked("eq", 2, 2);
lean_inc(x_2);
x_33 = l_Lean_Name_str___override(x_2, x_32);
x_34 = lean_nat_add(x_7, x_24);
x_35 = lean_name_append_index_after(x_33, x_34);
x_36 = lean_box(x_3);
lean_inc(x_4);
lean_inc(x_35);
lean_inc(x_2);
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_mkEqns_doRealize___boxed), 10, 5);
lean_closure_set(x_37, 0, x_2);
lean_closure_set(x_37, 1, x_36);
lean_closure_set(x_37, 2, x_35);
lean_closure_set(x_37, 3, x_4);
lean_closure_set(x_37, 4, x_25);
lean_inc(x_35);
lean_inc(x_2);
x_38 = l_Lean_Meta_realizeConst(x_2, x_35, x_37, x_27, x_28, x_29, x_30, x_31);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_array_push(x_26, x_35);
x_41 = lean_ctor_get(x_5, 2);
x_42 = lean_nat_add(x_7, x_41);
lean_dec(x_7);
x_6 = x_40;
x_7 = x_42;
x_12 = x_39;
goto _start;
}
else
{
uint8_t x_44; 
lean_dec(x_35);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
return x_38;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_38, 0);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_38);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_92; 
x_65 = lean_ctor_get(x_20, 0);
x_66 = lean_ctor_get(x_20, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_20);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_array_fget(x_1, x_7);
x_92 = lean_unbox(x_65);
lean_dec(x_65);
if (x_92 == 0)
{
lean_dec(x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_69 = x_6;
x_70 = x_8;
x_71 = x_9;
x_72 = x_10;
x_73 = x_11;
x_74 = x_66;
goto block_91;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_93 = lean_mk_string_unchecked("eqnType[", 8, 8);
x_94 = l_Lean_stringToMessageData(x_93);
lean_dec(x_93);
lean_inc(x_7);
x_95 = l___private_Init_Data_Repr_0__Nat_reprFast(x_7);
x_96 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = l_Lean_MessageData_ofFormat(x_96);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_94);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_mk_string_unchecked("]: ", 3, 3);
x_100 = l_Lean_stringToMessageData(x_99);
lean_dec(x_99);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_100);
lean_inc(x_68);
x_102 = l_Lean_MessageData_ofExpr(x_68);
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_mk_string_unchecked("", 0, 0);
x_105 = l_Lean_stringToMessageData(x_104);
lean_dec(x_104);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_19, x_106, x_8, x_9, x_10, x_11, x_66);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_69 = x_6;
x_70 = x_8;
x_71 = x_9;
x_72 = x_10;
x_73 = x_11;
x_74 = x_108;
goto block_91;
}
block_91:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = lean_mk_string_unchecked("eq", 2, 2);
lean_inc(x_2);
x_76 = l_Lean_Name_str___override(x_2, x_75);
x_77 = lean_nat_add(x_7, x_67);
x_78 = lean_name_append_index_after(x_76, x_77);
x_79 = lean_box(x_3);
lean_inc(x_4);
lean_inc(x_78);
lean_inc(x_2);
x_80 = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_mkEqns_doRealize___boxed), 10, 5);
lean_closure_set(x_80, 0, x_2);
lean_closure_set(x_80, 1, x_79);
lean_closure_set(x_80, 2, x_78);
lean_closure_set(x_80, 3, x_4);
lean_closure_set(x_80, 4, x_68);
lean_inc(x_78);
lean_inc(x_2);
x_81 = l_Lean_Meta_realizeConst(x_2, x_78, x_80, x_70, x_71, x_72, x_73, x_74);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_array_push(x_69, x_78);
x_84 = lean_ctor_get(x_5, 2);
x_85 = lean_nat_add(x_7, x_84);
lean_dec(x_7);
x_6 = x_83;
x_7 = x_85;
x_12 = x_82;
goto _start;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_78);
lean_dec(x_69);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_87 = lean_ctor_get(x_81, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_89 = x_81;
} else {
 lean_dec_ref(x_81);
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
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Eqns_mkEqns_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Eqns_mkEqns_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkEqns___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint64_t x_35; lean_object* x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint8_t x_40; uint64_t x_41; uint64_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_9 = lean_box(0);
lean_inc(x_4);
x_10 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_3, x_9, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_mvarId_x21(x_11);
lean_dec(x_11);
x_14 = lean_box(2);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_15, 0);
x_17 = lean_ctor_get_uint8(x_15, 1);
x_18 = lean_ctor_get_uint8(x_15, 2);
x_19 = lean_ctor_get_uint8(x_15, 3);
x_20 = lean_ctor_get_uint8(x_15, 4);
x_21 = lean_ctor_get_uint8(x_15, 5);
x_22 = lean_ctor_get_uint8(x_15, 6);
x_23 = lean_ctor_get_uint8(x_15, 7);
x_24 = lean_ctor_get_uint8(x_15, 8);
x_25 = lean_ctor_get_uint8(x_15, 10);
x_26 = lean_ctor_get_uint8(x_15, 11);
x_27 = lean_ctor_get_uint8(x_15, 12);
x_28 = lean_ctor_get_uint8(x_15, 13);
x_29 = lean_ctor_get_uint8(x_15, 14);
x_30 = lean_ctor_get_uint8(x_15, 15);
x_31 = lean_ctor_get_uint8(x_15, 16);
x_32 = lean_ctor_get_uint8(x_15, 17);
lean_dec(x_15);
x_33 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_33, 0, x_16);
lean_ctor_set_uint8(x_33, 1, x_17);
lean_ctor_set_uint8(x_33, 2, x_18);
lean_ctor_set_uint8(x_33, 3, x_19);
lean_ctor_set_uint8(x_33, 4, x_20);
lean_ctor_set_uint8(x_33, 5, x_21);
lean_ctor_set_uint8(x_33, 6, x_22);
lean_ctor_set_uint8(x_33, 7, x_23);
lean_ctor_set_uint8(x_33, 8, x_24);
x_34 = lean_unbox(x_14);
lean_ctor_set_uint8(x_33, 9, x_34);
lean_ctor_set_uint8(x_33, 10, x_25);
lean_ctor_set_uint8(x_33, 11, x_26);
lean_ctor_set_uint8(x_33, 12, x_27);
lean_ctor_set_uint8(x_33, 13, x_28);
lean_ctor_set_uint8(x_33, 14, x_29);
lean_ctor_set_uint8(x_33, 15, x_30);
lean_ctor_set_uint8(x_33, 16, x_31);
lean_ctor_set_uint8(x_33, 17, x_32);
x_35 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_uint64_of_nat(x_36);
x_38 = lean_uint64_shift_right(x_35, x_37);
x_39 = lean_uint64_shift_left(x_38, x_37);
x_40 = lean_unbox(x_14);
x_41 = l_Lean_Meta_TransparencyMode_toUInt64(x_40);
x_42 = lean_uint64_lor(x_39, x_41);
x_43 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_44 = lean_ctor_get(x_4, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_4, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_4, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_4, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_4, 5);
lean_inc(x_48);
x_49 = lean_ctor_get(x_4, 6);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_51 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
lean_dec(x_4);
x_52 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_52, 0, x_33);
lean_ctor_set(x_52, 1, x_44);
lean_ctor_set(x_52, 2, x_45);
lean_ctor_set(x_52, 3, x_46);
lean_ctor_set(x_52, 4, x_47);
lean_ctor_set(x_52, 5, x_48);
lean_ctor_set(x_52, 6, x_49);
lean_ctor_set_uint64(x_52, sizeof(void*)*7, x_42);
lean_ctor_set_uint8(x_52, sizeof(void*)*7 + 8, x_43);
lean_ctor_set_uint8(x_52, sizeof(void*)*7 + 9, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*7 + 10, x_51);
x_53 = l_Lean_Elab_Eqns_mkEqnTypes(x_1, x_13, x_52, x_5, x_6, x_7, x_12);
return x_53;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkEqns(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_getConstInfoDefn___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldThmType_spec__0(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_99; uint8_t x_100; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_mkEqns___lam__0___boxed), 8, 1);
lean_closure_set(x_15, 0, x_2);
x_16 = lean_ctor_get(x_6, 2);
lean_inc(x_16);
x_17 = l_Lean_Meta_tactic_hygienic;
x_18 = lean_box(0);
x_19 = l_Lean_diagnostics;
x_20 = lean_unbox(x_18);
x_21 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_16, x_17, x_20);
x_22 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_21, x_19);
x_99 = lean_ctor_get(x_13, 0);
lean_inc(x_99);
lean_dec(x_13);
x_100 = l_Lean_Kernel_isDiagnosticsEnabled(x_99);
lean_dec(x_99);
if (x_100 == 0)
{
if (x_22 == 0)
{
x_23 = x_6;
x_24 = x_7;
x_25 = x_14;
goto block_64;
}
else
{
goto block_98;
}
}
else
{
if (x_22 == 0)
{
goto block_98;
}
else
{
x_23 = x_6;
x_24 = x_7;
x_25 = x_14;
goto block_64;
}
}
block_64:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 3);
lean_inc(x_28);
x_29 = l_Lean_maxRecDepth;
x_30 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_21, x_29);
x_31 = lean_ctor_get(x_23, 5);
lean_inc(x_31);
x_32 = lean_ctor_get(x_23, 6);
lean_inc(x_32);
x_33 = lean_ctor_get(x_23, 7);
lean_inc(x_33);
x_34 = lean_ctor_get(x_23, 8);
lean_inc(x_34);
x_35 = lean_ctor_get(x_23, 9);
lean_inc(x_35);
x_36 = lean_ctor_get(x_23, 10);
lean_inc(x_36);
x_37 = lean_ctor_get(x_23, 11);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_23, sizeof(void*)*13 + 1);
x_39 = lean_ctor_get(x_23, 12);
lean_inc(x_39);
lean_dec(x_23);
x_40 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_27);
lean_ctor_set(x_40, 2, x_21);
lean_ctor_set(x_40, 3, x_28);
lean_ctor_set(x_40, 4, x_30);
lean_ctor_set(x_40, 5, x_31);
lean_ctor_set(x_40, 6, x_32);
lean_ctor_set(x_40, 7, x_33);
lean_ctor_set(x_40, 8, x_34);
lean_ctor_set(x_40, 9, x_35);
lean_ctor_set(x_40, 10, x_36);
lean_ctor_set(x_40, 11, x_37);
lean_ctor_set(x_40, 12, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*13, x_22);
lean_ctor_set_uint8(x_40, sizeof(void*)*13 + 1, x_38);
lean_inc(x_24);
lean_inc(x_40);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_41 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldThmType(x_1, x_4, x_5, x_40, x_24, x_25);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_box(1);
x_45 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___boxed), 9, 4);
lean_closure_set(x_45, 0, lean_box(0));
lean_closure_set(x_45, 1, x_42);
lean_closure_set(x_45, 2, x_15);
lean_closure_set(x_45, 3, x_44);
x_46 = lean_unbox(x_18);
lean_inc(x_24);
lean_inc(x_40);
lean_inc(x_5);
lean_inc(x_4);
x_47 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_45, x_46, x_4, x_5, x_40, x_24, x_43);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_mk_empty_array_with_capacity(x_50);
x_52 = lean_array_get_size(x_48);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_52);
lean_ctor_set(x_54, 2, x_53);
x_55 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Eqns_mkEqns_spec__0___redArg(x_48, x_1, x_3, x_10, x_54, x_51, x_50, x_4, x_5, x_40, x_24, x_49);
lean_dec(x_54);
lean_dec(x_48);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_40);
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_47);
if (x_56 == 0)
{
return x_47;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_47, 0);
x_58 = lean_ctor_get(x_47, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_47);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_40);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_41);
if (x_60 == 0)
{
return x_41;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_41, 0);
x_62 = lean_ctor_get(x_41, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_41);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
block_98:
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_st_ref_take(x_7, x_14);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_65, 1);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = l_Lean_Kernel_enableDiag(x_69, x_22);
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_67, 3);
lean_inc(x_73);
x_74 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
lean_inc(x_75);
lean_ctor_set(x_65, 1, x_75);
lean_ctor_set(x_65, 0, x_75);
x_76 = lean_ctor_get(x_67, 5);
lean_inc(x_76);
x_77 = lean_ctor_get(x_67, 6);
lean_inc(x_77);
x_78 = lean_ctor_get(x_67, 7);
lean_inc(x_78);
lean_dec(x_67);
x_79 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_79, 0, x_70);
lean_ctor_set(x_79, 1, x_71);
lean_ctor_set(x_79, 2, x_72);
lean_ctor_set(x_79, 3, x_73);
lean_ctor_set(x_79, 4, x_65);
lean_ctor_set(x_79, 5, x_76);
lean_ctor_set(x_79, 6, x_77);
lean_ctor_set(x_79, 7, x_78);
x_80 = lean_st_ref_set(x_7, x_79, x_68);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_23 = x_6;
x_24 = x_7;
x_25 = x_81;
goto block_64;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_82 = lean_ctor_get(x_65, 0);
x_83 = lean_ctor_get(x_65, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_65);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
x_85 = l_Lean_Kernel_enableDiag(x_84, x_22);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_82, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_82, 3);
lean_inc(x_88);
x_89 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_89);
lean_inc(x_90);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_ctor_get(x_82, 5);
lean_inc(x_92);
x_93 = lean_ctor_get(x_82, 6);
lean_inc(x_93);
x_94 = lean_ctor_get(x_82, 7);
lean_inc(x_94);
lean_dec(x_82);
x_95 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_95, 0, x_85);
lean_ctor_set(x_95, 1, x_86);
lean_ctor_set(x_95, 2, x_87);
lean_ctor_set(x_95, 3, x_88);
lean_ctor_set(x_95, 4, x_91);
lean_ctor_set(x_95, 5, x_92);
lean_ctor_set(x_95, 6, x_93);
lean_ctor_set(x_95, 7, x_94);
x_96 = lean_st_ref_set(x_7, x_95, x_83);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_23 = x_6;
x_24 = x_7;
x_25 = x_97;
goto block_64;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_9);
if (x_101 == 0)
{
return x_9;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_9, 0);
x_103 = lean_ctor_get(x_9, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_9);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Eqns_mkEqns_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Eqns_mkEqns_spec__0___redArg(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Eqns_mkEqns_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Eqns_mkEqns_spec__0(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkEqns___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Eqns_mkEqns___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkEqns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Elab_Eqns_mkEqns(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___Lean_Elab_Eqns_mkUnfoldProof_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_Elab_Eqns_mkUnfoldProof_go(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_3 = x_12;
x_8 = x_14;
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkUnfoldProof_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_57; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_57 = lean_unbox(x_11);
if (x_57 == 0)
{
lean_object* x_58; 
lean_free_object(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_58 = l_Lean_MVarId_getType_x27(x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_61 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch(x_59, x_4, x_5, x_6, x_7, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_64;
goto block_56;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_dec(x_61);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_66 = l_Lean_Elab_Eqns_simpMatch_x3f(x_3, x_4, x_5, x_6, x_7, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_68;
goto block_56;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_11);
lean_dec(x_3);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
lean_dec(x_67);
x_3 = x_70;
x_8 = x_69;
goto _start;
}
}
else
{
uint8_t x_72; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_66);
if (x_72 == 0)
{
return x_66;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_66, 0);
x_74 = lean_ctor_get(x_66, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_66);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_61);
if (x_76 == 0)
{
return x_61;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_61, 0);
x_78 = lean_ctor_get(x_61, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_61);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_58);
if (x_80 == 0)
{
return x_58;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_58, 0);
x_82 = lean_ctor_get(x_58, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_58);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = lean_box(0);
lean_ctor_set(x_9, 0, x_84);
return x_9;
}
block_56:
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_11);
lean_dec(x_11);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_3);
x_19 = l_Lean_Meta_splitTarget_x3f(x_3, x_18, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_3);
x_22 = l_Lean_Elab_Eqns_tryContradiction(x_3, x_13, x_14, x_15, x_16, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_mk_string_unchecked("failed to generate unfold theorem for '", 39, 39);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = l_Lean_MessageData_ofName(x_1);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_mk_string_unchecked("'\n", 2, 2);
x_31 = l_Lean_stringToMessageData(x_30);
lean_dec(x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_3);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_mk_string_unchecked("", 0, 0);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_37, x_13, x_14, x_15, x_16, x_25);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_22);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_22, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_22, 0, x_41);
return x_22;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_22, 1);
lean_inc(x_42);
lean_dec(x_22);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_22);
if (x_45 == 0)
{
return x_22;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_22, 0);
x_47 = lean_ctor_get(x_22, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_22);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_3);
x_49 = lean_ctor_get(x_19, 1);
lean_inc(x_49);
lean_dec(x_19);
x_50 = lean_ctor_get(x_20, 0);
lean_inc(x_50);
lean_dec(x_20);
x_51 = l_List_forM___at___Lean_Elab_Eqns_mkUnfoldProof_go_spec__0(x_1, x_2, x_50, x_13, x_14, x_15, x_16, x_49);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_19);
if (x_52 == 0)
{
return x_19;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_19, 0);
x_54 = lean_ctor_get(x_19, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_19);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_129; 
x_85 = lean_ctor_get(x_9, 0);
x_86 = lean_ctor_get(x_9, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_9);
x_129 = lean_unbox(x_85);
if (x_129 == 0)
{
lean_object* x_130; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_130 = l_Lean_MVarId_getType_x27(x_3, x_4, x_5, x_6, x_7, x_86);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_133 = l___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_shouldUseSimpMatch(x_131, x_4, x_5, x_6, x_7, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_unbox(x_134);
lean_dec(x_134);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
x_87 = x_4;
x_88 = x_5;
x_89 = x_6;
x_90 = x_7;
x_91 = x_136;
goto block_128;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_133, 1);
lean_inc(x_137);
lean_dec(x_133);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_138 = l_Lean_Elab_Eqns_simpMatch_x3f(x_3, x_4, x_5, x_6, x_7, x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_87 = x_4;
x_88 = x_5;
x_89 = x_6;
x_90 = x_7;
x_91 = x_140;
goto block_128;
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_85);
lean_dec(x_3);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = lean_ctor_get(x_139, 0);
lean_inc(x_142);
lean_dec(x_139);
x_3 = x_142;
x_8 = x_141;
goto _start;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_85);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_144 = lean_ctor_get(x_138, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_138, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_146 = x_138;
} else {
 lean_dec_ref(x_138);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_85);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_148 = lean_ctor_get(x_133, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_133, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_150 = x_133;
} else {
 lean_dec_ref(x_133);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_85);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_152 = lean_ctor_get(x_130, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_130, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_154 = x_130;
} else {
 lean_dec_ref(x_130);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_85);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_86);
return x_157;
}
block_128:
{
uint8_t x_92; lean_object* x_93; 
x_92 = lean_unbox(x_85);
lean_dec(x_85);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_3);
x_93 = l_Lean_Meta_splitTarget_x3f(x_3, x_92, x_87, x_88, x_89, x_90, x_91);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_2);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_3);
x_96 = l_Lean_Elab_Eqns_tryContradiction(x_3, x_87, x_88, x_89, x_90, x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_unbox(x_97);
lean_dec(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_100 = lean_mk_string_unchecked("failed to generate unfold theorem for '", 39, 39);
x_101 = l_Lean_stringToMessageData(x_100);
lean_dec(x_100);
x_102 = l_Lean_MessageData_ofName(x_1);
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_mk_string_unchecked("'\n", 2, 2);
x_105 = l_Lean_stringToMessageData(x_104);
lean_dec(x_104);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_3);
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_mk_string_unchecked("", 0, 0);
x_110 = l_Lean_stringToMessageData(x_109);
lean_dec(x_109);
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_111, x_87, x_88, x_89, x_90, x_99);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_3);
lean_dec(x_1);
x_113 = lean_ctor_get(x_96, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_114 = x_96;
} else {
 lean_dec_ref(x_96);
 x_114 = lean_box(0);
}
x_115 = lean_box(0);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_3);
lean_dec(x_1);
x_117 = lean_ctor_get(x_96, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_96, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_119 = x_96;
} else {
 lean_dec_ref(x_96);
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
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_3);
x_121 = lean_ctor_get(x_93, 1);
lean_inc(x_121);
lean_dec(x_93);
x_122 = lean_ctor_get(x_94, 0);
lean_inc(x_122);
lean_dec(x_94);
x_123 = l_List_forM___at___Lean_Elab_Eqns_mkUnfoldProof_go_spec__0(x_1, x_2, x_122, x_87, x_88, x_89, x_90, x_121);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = lean_ctor_get(x_93, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_93, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_126 = x_93;
} else {
 lean_dec_ref(x_93);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_9);
if (x_158 == 0)
{
return x_9;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_9, 0);
x_160 = lean_ctor_get(x_9, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_9);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___Lean_Elab_Eqns_mkUnfoldProof_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_17 = l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0(x_9, x_2, x_3, x_4, x_5, x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_21 = l_Lean_MVarId_assumptionCore(x_9, x_2, x_3, x_4, x_5, x_20);
x_11 = x_21;
goto block_16;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_1 = x_10;
x_6 = x_22;
goto _start;
}
block_16:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_1 = x_10;
x_6 = x_14;
goto _start;
}
}
else
{
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___Lean_Elab_Eqns_mkUnfoldProof_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_23; lean_object* x_24; uint8_t x_28; lean_object* x_29; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_9 = l_Lean_Meta_saveState___redArg(x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_50 = lean_st_ref_take(x_5, x_11);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_51, 1);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_57 = lean_ctor_get(x_52, 4);
lean_dec(x_57);
x_58 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_52, 4, x_59);
x_60 = lean_st_ref_set(x_5, x_51, x_53);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = l_Lean_Meta_getResetPostponed(x_4, x_5, x_6, x_7, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_1, x_4, x_5, x_6, x_7, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_box(0);
x_69 = lean_box(1);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 0, 4);
x_72 = lean_unbox(x_68);
lean_ctor_set_uint8(x_71, 0, x_72);
x_73 = lean_unbox(x_69);
lean_ctor_set_uint8(x_71, 1, x_73);
x_74 = lean_unbox(x_70);
lean_ctor_set_uint8(x_71, 2, x_74);
x_75 = lean_unbox(x_69);
lean_ctor_set_uint8(x_71, 3, x_75);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_76 = l_Lean_MVarId_apply(x_2, x_66, x_71, x_4, x_5, x_6, x_7, x_67);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_79 = l_List_allM___at___Lean_Elab_Eqns_mkUnfoldProof_spec__0(x_77, x_4, x_5, x_6, x_7, x_78);
if (lean_obj_tag(x_79) == 0)
{
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; 
lean_dec(x_63);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_unbox(x_80);
lean_dec(x_80);
x_28 = x_83;
x_29 = x_82;
goto block_37;
}
else
{
lean_object* x_84; uint8_t x_85; lean_object* x_86; 
lean_dec(x_80);
x_84 = lean_ctor_get(x_79, 1);
lean_inc(x_84);
lean_dec(x_79);
x_85 = lean_unbox(x_70);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_86 = l_Lean_Meta_processPostponed(x_3, x_85, x_4, x_5, x_6, x_7, x_84);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; uint8_t x_88; 
lean_dec(x_12);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
lean_dec(x_87);
lean_dec(x_63);
lean_dec(x_6);
lean_dec(x_4);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = l_Lean_Meta_SavedState_restore___redArg(x_10, x_5, x_7, x_89);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_10);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_90, 0);
lean_dec(x_92);
lean_ctor_set(x_90, 0, x_70);
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_70);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_dec(x_10);
x_95 = lean_ctor_get(x_86, 1);
lean_inc(x_95);
lean_dec(x_86);
x_96 = l_Lean_Meta_getPostponed___redArg(x_5, x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l_Lean_PersistentArray_append___redArg(x_63, x_97);
lean_dec(x_97);
x_100 = l_Lean_Meta_setPostponed(x_99, x_4, x_5, x_6, x_7, x_98);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_100, 0);
lean_dec(x_102);
lean_ctor_set(x_100, 0, x_87);
return x_100;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_87);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_63);
lean_dec(x_6);
lean_dec(x_4);
x_105 = lean_ctor_get(x_86, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_86, 1);
lean_inc(x_106);
lean_dec(x_86);
x_23 = x_105;
x_24 = x_106;
goto block_27;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_63);
lean_dec(x_6);
lean_dec(x_4);
x_107 = lean_ctor_get(x_79, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_79, 1);
lean_inc(x_108);
lean_dec(x_79);
x_23 = x_107;
x_24 = x_108;
goto block_27;
}
}
else
{
uint8_t x_109; 
lean_dec(x_63);
lean_dec(x_6);
lean_dec(x_4);
x_109 = !lean_is_exclusive(x_79);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_79, 0);
x_111 = lean_ctor_get(x_79, 1);
lean_inc(x_111);
lean_inc(x_110);
x_44 = x_79;
x_45 = x_110;
x_46 = x_111;
goto block_49;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_79, 0);
x_113 = lean_ctor_get(x_79, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_79);
lean_inc(x_113);
lean_inc(x_112);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_44 = x_114;
x_45 = x_112;
x_46 = x_113;
goto block_49;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_63);
lean_dec(x_6);
lean_dec(x_4);
x_115 = !lean_is_exclusive(x_76);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_76, 0);
x_117 = lean_ctor_get(x_76, 1);
lean_inc(x_117);
lean_inc(x_116);
x_44 = x_76;
x_45 = x_116;
x_46 = x_117;
goto block_49;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_76, 0);
x_119 = lean_ctor_get(x_76, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_76);
lean_inc(x_119);
lean_inc(x_118);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_44 = x_120;
x_45 = x_118;
x_46 = x_119;
goto block_49;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_63);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_65);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_65, 0);
x_123 = lean_ctor_get(x_65, 1);
lean_inc(x_123);
lean_inc(x_122);
x_44 = x_65;
x_45 = x_122;
x_46 = x_123;
goto block_49;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_65, 0);
x_125 = lean_ctor_get(x_65, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_65);
lean_inc(x_125);
lean_inc(x_124);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_44 = x_126;
x_45 = x_124;
x_46 = x_125;
goto block_49;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_127 = lean_ctor_get(x_52, 0);
x_128 = lean_ctor_get(x_52, 1);
x_129 = lean_ctor_get(x_52, 2);
x_130 = lean_ctor_get(x_52, 3);
x_131 = lean_ctor_get(x_52, 5);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_52);
x_132 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_134, 0, x_127);
lean_ctor_set(x_134, 1, x_128);
lean_ctor_set(x_134, 2, x_129);
lean_ctor_set(x_134, 3, x_130);
lean_ctor_set(x_134, 4, x_133);
lean_ctor_set(x_134, 5, x_131);
lean_ctor_set(x_51, 1, x_134);
x_135 = lean_st_ref_set(x_5, x_51, x_53);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_137 = l_Lean_Meta_getResetPostponed(x_4, x_5, x_6, x_7, x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_1, x_4, x_5, x_6, x_7, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; lean_object* x_151; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_box(0);
x_144 = lean_box(1);
x_145 = lean_box(0);
x_146 = lean_alloc_ctor(0, 0, 4);
x_147 = lean_unbox(x_143);
lean_ctor_set_uint8(x_146, 0, x_147);
x_148 = lean_unbox(x_144);
lean_ctor_set_uint8(x_146, 1, x_148);
x_149 = lean_unbox(x_145);
lean_ctor_set_uint8(x_146, 2, x_149);
x_150 = lean_unbox(x_144);
lean_ctor_set_uint8(x_146, 3, x_150);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_151 = l_Lean_MVarId_apply(x_2, x_141, x_146, x_4, x_5, x_6, x_7, x_142);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_154 = l_List_allM___at___Lean_Elab_Eqns_mkUnfoldProof_spec__0(x_152, x_4, x_5, x_6, x_7, x_153);
if (lean_obj_tag(x_154) == 0)
{
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; uint8_t x_156; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_unbox(x_155);
if (x_156 == 0)
{
lean_object* x_157; uint8_t x_158; 
lean_dec(x_138);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
lean_dec(x_154);
x_158 = lean_unbox(x_155);
lean_dec(x_155);
x_28 = x_158;
x_29 = x_157;
goto block_37;
}
else
{
lean_object* x_159; uint8_t x_160; lean_object* x_161; 
lean_dec(x_155);
x_159 = lean_ctor_get(x_154, 1);
lean_inc(x_159);
lean_dec(x_154);
x_160 = lean_unbox(x_145);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_161 = l_Lean_Meta_processPostponed(x_3, x_160, x_4, x_5, x_6, x_7, x_159);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; uint8_t x_163; 
lean_dec(x_12);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_unbox(x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_162);
lean_dec(x_138);
lean_dec(x_6);
lean_dec(x_4);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
lean_dec(x_161);
x_165 = l_Lean_Meta_SavedState_restore___redArg(x_10, x_5, x_7, x_164);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_10);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_167 = x_165;
} else {
 lean_dec_ref(x_165);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_145);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_10);
x_169 = lean_ctor_get(x_161, 1);
lean_inc(x_169);
lean_dec(x_161);
x_170 = l_Lean_Meta_getPostponed___redArg(x_5, x_169);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = l_Lean_PersistentArray_append___redArg(x_138, x_171);
lean_dec(x_171);
x_174 = l_Lean_Meta_setPostponed(x_173, x_4, x_5, x_6, x_7, x_172);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_176 = x_174;
} else {
 lean_dec_ref(x_174);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_162);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_138);
lean_dec(x_6);
lean_dec(x_4);
x_178 = lean_ctor_get(x_161, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_161, 1);
lean_inc(x_179);
lean_dec(x_161);
x_23 = x_178;
x_24 = x_179;
goto block_27;
}
}
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_138);
lean_dec(x_6);
lean_dec(x_4);
x_180 = lean_ctor_get(x_154, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_154, 1);
lean_inc(x_181);
lean_dec(x_154);
x_23 = x_180;
x_24 = x_181;
goto block_27;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_138);
lean_dec(x_6);
lean_dec(x_4);
x_182 = lean_ctor_get(x_154, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_154, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_184 = x_154;
} else {
 lean_dec_ref(x_154);
 x_184 = lean_box(0);
}
lean_inc(x_183);
lean_inc(x_182);
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
x_44 = x_185;
x_45 = x_182;
x_46 = x_183;
goto block_49;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_138);
lean_dec(x_6);
lean_dec(x_4);
x_186 = lean_ctor_get(x_151, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_151, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_188 = x_151;
} else {
 lean_dec_ref(x_151);
 x_188 = lean_box(0);
}
lean_inc(x_187);
lean_inc(x_186);
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
x_44 = x_189;
x_45 = x_186;
x_46 = x_187;
goto block_49;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_138);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_190 = lean_ctor_get(x_140, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_140, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_192 = x_140;
} else {
 lean_dec_ref(x_140);
 x_192 = lean_box(0);
}
lean_inc(x_191);
lean_inc(x_190);
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
x_44 = x_193;
x_45 = x_190;
x_46 = x_191;
goto block_49;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_194 = lean_ctor_get(x_51, 0);
x_195 = lean_ctor_get(x_51, 2);
x_196 = lean_ctor_get(x_51, 3);
x_197 = lean_ctor_get(x_51, 4);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_51);
x_198 = lean_ctor_get(x_52, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_52, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_52, 2);
lean_inc(x_200);
x_201 = lean_ctor_get(x_52, 3);
lean_inc(x_201);
x_202 = lean_ctor_get(x_52, 5);
lean_inc(x_202);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 lean_ctor_release(x_52, 5);
 x_203 = x_52;
} else {
 lean_dec_ref(x_52);
 x_203 = lean_box(0);
}
x_204 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_204);
if (lean_is_scalar(x_203)) {
 x_206 = lean_alloc_ctor(0, 6, 0);
} else {
 x_206 = x_203;
}
lean_ctor_set(x_206, 0, x_198);
lean_ctor_set(x_206, 1, x_199);
lean_ctor_set(x_206, 2, x_200);
lean_ctor_set(x_206, 3, x_201);
lean_ctor_set(x_206, 4, x_205);
lean_ctor_set(x_206, 5, x_202);
x_207 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_207, 0, x_194);
lean_ctor_set(x_207, 1, x_206);
lean_ctor_set(x_207, 2, x_195);
lean_ctor_set(x_207, 3, x_196);
lean_ctor_set(x_207, 4, x_197);
x_208 = lean_st_ref_set(x_5, x_207, x_53);
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
lean_dec(x_208);
x_210 = l_Lean_Meta_getResetPostponed(x_4, x_5, x_6, x_7, x_209);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_213 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_1, x_4, x_5, x_6, x_7, x_212);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; uint8_t x_221; uint8_t x_222; uint8_t x_223; lean_object* x_224; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_box(0);
x_217 = lean_box(1);
x_218 = lean_box(0);
x_219 = lean_alloc_ctor(0, 0, 4);
x_220 = lean_unbox(x_216);
lean_ctor_set_uint8(x_219, 0, x_220);
x_221 = lean_unbox(x_217);
lean_ctor_set_uint8(x_219, 1, x_221);
x_222 = lean_unbox(x_218);
lean_ctor_set_uint8(x_219, 2, x_222);
x_223 = lean_unbox(x_217);
lean_ctor_set_uint8(x_219, 3, x_223);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_224 = l_Lean_MVarId_apply(x_2, x_214, x_219, x_4, x_5, x_6, x_7, x_215);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_227 = l_List_allM___at___Lean_Elab_Eqns_mkUnfoldProof_spec__0(x_225, x_4, x_5, x_6, x_7, x_226);
if (lean_obj_tag(x_227) == 0)
{
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; uint8_t x_229; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_unbox(x_228);
if (x_229 == 0)
{
lean_object* x_230; uint8_t x_231; 
lean_dec(x_211);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
x_230 = lean_ctor_get(x_227, 1);
lean_inc(x_230);
lean_dec(x_227);
x_231 = lean_unbox(x_228);
lean_dec(x_228);
x_28 = x_231;
x_29 = x_230;
goto block_37;
}
else
{
lean_object* x_232; uint8_t x_233; lean_object* x_234; 
lean_dec(x_228);
x_232 = lean_ctor_get(x_227, 1);
lean_inc(x_232);
lean_dec(x_227);
x_233 = lean_unbox(x_218);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_234 = l_Lean_Meta_processPostponed(x_3, x_233, x_4, x_5, x_6, x_7, x_232);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; uint8_t x_236; 
lean_dec(x_12);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_unbox(x_235);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_235);
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
x_237 = lean_ctor_get(x_234, 1);
lean_inc(x_237);
lean_dec(x_234);
x_238 = l_Lean_Meta_SavedState_restore___redArg(x_10, x_5, x_7, x_237);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_10);
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_240 = x_238;
} else {
 lean_dec_ref(x_238);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_218);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_10);
x_242 = lean_ctor_get(x_234, 1);
lean_inc(x_242);
lean_dec(x_234);
x_243 = l_Lean_Meta_getPostponed___redArg(x_5, x_242);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = l_Lean_PersistentArray_append___redArg(x_211, x_244);
lean_dec(x_244);
x_247 = l_Lean_Meta_setPostponed(x_246, x_4, x_5, x_6, x_7, x_245);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_248 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_249 = x_247;
} else {
 lean_dec_ref(x_247);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_235);
lean_ctor_set(x_250, 1, x_248);
return x_250;
}
}
else
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
x_251 = lean_ctor_get(x_234, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_234, 1);
lean_inc(x_252);
lean_dec(x_234);
x_23 = x_251;
x_24 = x_252;
goto block_27;
}
}
}
else
{
lean_object* x_253; lean_object* x_254; 
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
x_253 = lean_ctor_get(x_227, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_227, 1);
lean_inc(x_254);
lean_dec(x_227);
x_23 = x_253;
x_24 = x_254;
goto block_27;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
x_255 = lean_ctor_get(x_227, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_227, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_257 = x_227;
} else {
 lean_dec_ref(x_227);
 x_257 = lean_box(0);
}
lean_inc(x_256);
lean_inc(x_255);
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_256);
x_44 = x_258;
x_45 = x_255;
x_46 = x_256;
goto block_49;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
x_259 = lean_ctor_get(x_224, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_224, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_261 = x_224;
} else {
 lean_dec_ref(x_224);
 x_261 = lean_box(0);
}
lean_inc(x_260);
lean_inc(x_259);
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set(x_262, 1, x_260);
x_44 = x_262;
x_45 = x_259;
x_46 = x_260;
goto block_49;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_211);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_263 = lean_ctor_get(x_213, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_213, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_265 = x_213;
} else {
 lean_dec_ref(x_213);
 x_265 = lean_box(0);
}
lean_inc(x_264);
lean_inc(x_263);
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
x_44 = x_266;
x_45 = x_263;
x_46 = x_264;
goto block_49;
}
}
block_22:
{
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_12);
x_16 = l_Lean_Meta_SavedState_restore___redArg(x_10, x_5, x_7, x_14);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
if (lean_is_scalar(x_12)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_12;
 lean_ctor_set_tag(x_21, 1);
}
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
return x_21;
}
}
block_27:
{
uint8_t x_25; 
x_25 = l_Lean_Exception_isInterrupt(x_23);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Exception_isRuntime(x_23);
x_13 = x_23;
x_14 = x_24;
x_15 = x_26;
goto block_22;
}
else
{
x_13 = x_23;
x_14 = x_24;
x_15 = x_25;
goto block_22;
}
}
block_37:
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Meta_SavedState_restore___redArg(x_10, x_5, x_7, x_29);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_10);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_box(x_28);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_box(x_28);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
block_43:
{
if (x_40 == 0)
{
lean_dec(x_38);
lean_dec(x_12);
x_28 = x_40;
x_29 = x_39;
goto block_37;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_39);
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_23 = x_41;
x_24 = x_42;
goto block_27;
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
lean_dec(x_45);
x_38 = x_44;
x_39 = x_46;
x_40 = x_48;
goto block_43;
}
else
{
lean_dec(x_45);
x_38 = x_44;
x_39 = x_46;
x_40 = x_47;
goto block_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___Lean_Elab_Eqns_mkUnfoldProof_spec__2_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_3, x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_uget(x_2, x_3);
x_12 = lean_box(x_10);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_checkpointDefEq___at___Lean_Elab_Eqns_mkUnfoldProof_spec__1___boxed), 8, 3);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_commitWhen___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
lean_dec(x_15);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_9 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_14, 0);
lean_dec(x_23);
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Eqns_mkUnfoldProof_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_3, x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_uget(x_2, x_3);
x_12 = lean_box(x_10);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_checkpointDefEq___at___Lean_Elab_Eqns_mkUnfoldProof_spec__1___boxed), 8, 3);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_commitWhen___at_____private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
lean_dec(x_15);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_3, x_19);
x_21 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___Lean_Elab_Eqns_mkUnfoldProof_spec__2_spec__2(x_1, x_2, x_20, x_4, x_5, x_6, x_7, x_8, x_17);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_14, 0);
lean_dec(x_23);
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkUnfoldProof___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
if (x_10 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_usize_of_nat(x_8);
x_16 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_17 = l_Array_anyMUnsafe_any___at___Lean_Elab_Eqns_mkUnfoldProof_spec__2(x_2, x_1, x_15, x_16, x_3, x_4, x_5, x_6, x_7);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkUnfoldProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_8 = l_Lean_Meta_getEqnsFor_x3f(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_mk_string_unchecked("failed to generate equations for '", 34, 34);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = l_Lean_MessageData_ofName(x_1);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_mk_string_unchecked("'", 1, 1);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_17, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_mkUnfoldProof___lam__0___boxed), 7, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = l_Lean_Elab_Eqns_mkUnfoldProof_go(x_1, x_21, x_2, x_3, x_4, x_5, x_6, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
return x_8;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___Lean_Elab_Eqns_mkUnfoldProof_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_allM___at___Lean_Elab_Eqns_mkUnfoldProof_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at___Lean_Elab_Eqns_mkUnfoldProof_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_checkpointDefEq___at___Lean_Elab_Eqns_mkUnfoldProof_spec__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___Lean_Elab_Eqns_mkUnfoldProof_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___Lean_Elab_Eqns_mkUnfoldProof_spec__2_spec__2(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Eqns_mkUnfoldProof_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_anyMUnsafe_any___at___Lean_Elab_Eqns_mkUnfoldProof_spec__2(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_mkUnfoldProof___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Eqns_mkUnfoldProof___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_initFn____x40_Lean_Elab_PreDefinition_Eqns___hyg_7734_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_2 = lean_mk_string_unchecked("Elab", 4, 4);
x_3 = lean_mk_string_unchecked("definition", 10, 10);
x_4 = lean_mk_string_unchecked("unfoldEqn", 9, 9);
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_8);
x_9 = l_Lean_Name_str___override(x_7, x_8);
lean_inc(x_2);
x_10 = l_Lean_Name_str___override(x_9, x_2);
x_11 = lean_mk_string_unchecked("Eqns", 4, 4);
lean_inc(x_11);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("initFn", 6, 6);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = lean_mk_string_unchecked("_@", 2, 2);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = l_Lean_Name_str___override(x_16, x_8);
lean_inc(x_2);
x_18 = l_Lean_Name_str___override(x_17, x_2);
x_19 = lean_mk_string_unchecked("PreDefinition", 13, 13);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = l_Lean_Name_str___override(x_20, x_11);
x_22 = lean_mk_string_unchecked("_hyg", 4, 4);
x_23 = l_Lean_Name_str___override(x_21, x_22);
x_24 = lean_unsigned_to_nat(7734u);
x_25 = l_Lean_Name_num___override(x_23, x_24);
x_26 = lean_unbox(x_6);
lean_inc(x_25);
x_27 = l_Lean_registerTraceClass(x_5, x_26, x_25, x_1);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_mk_string_unchecked("eqns", 4, 4);
x_30 = l_Lean_Name_mkStr3(x_2, x_3, x_29);
x_31 = lean_unbox(x_6);
x_32 = l_Lean_registerTraceClass(x_30, x_31, x_25, x_28);
return x_32;
}
else
{
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_2);
return x_27;
}
}
}
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CtorRecognizer(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_ForEachExprWhere(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Split(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatchEqs(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Eqns(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CtorRecognizer(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectFVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExprWhere(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Split(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatchEqs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Eqns_instInhabitedEqnInfoCore = _init_l_Lean_Elab_Eqns_instInhabitedEqnInfoCore();
lean_mark_persistent(l_Lean_Elab_Eqns_instInhabitedEqnInfoCore);
if (builtin) {res = l_Lean_Elab_Eqns_initFn____x40_Lean_Elab_PreDefinition_Eqns___hyg_7734_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
