// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Rewrite
// Imports: Lean.Meta.ACLt Lean.Meta.Match.MatchEqsExt Lean.Meta.AppBuilder Lean.Meta.SynthInstance Lean.Meta.Tactic.Util Lean.Meta.Tactic.UnifyEq Lean.Meta.Tactic.Simp.Types Lean.Meta.Tactic.Simp.Arith Lean.Meta.Tactic.Simp.Simproc Lean.Meta.Tactic.Simp.Attr Lean.Meta.BinderNameHint
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
lean_object* l_Lean_Meta_Simp_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSEvalMethods(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_sevalGround_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePost(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_useImplicitDefEqProof___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorem_getValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSEvalTheorems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___Lean_Meta_Simp_discharge_x3f_x27_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_useImplicitDefEqProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_SimpTheoremsArray_isErased(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DischargeResult_ofNat___boxed(lean_object*);
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Meta_unifyEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDefaultMethods___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
double lean_float_div(double, double);
uint8_t l_Lean_Meta_Simp_Arith_isDvdCnstr(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_discharge_x3f_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preDefault___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isEqnThmHypothesis_go___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DischargeResult_noConfusion___redArg(uint8_t, uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg___lam__1(lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isEqnThmHypothesis___boxed(lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simpMatchCore_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_discharge_x3f_x27___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_drewritePost_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_seval___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
extern uint8_t l_instInhabitedBool;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_drewritePre_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DischargeResult_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postSEval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__1_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_Simp_dischargeRfl_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t lean_float_decLt(double, double);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isMatcher___at___Lean_Meta_Simp_mkCongrSimp_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DischargeResult_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeRfl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_stripArgsN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_Expr_getAppArgsN_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dpreDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preSEval___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_resolveBinderNameHint(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___Lean_Meta_Simp_discharge_x3f_x27_spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewritePre_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f_inErasedSet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheorem_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preDefault___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_instDecidableEqDischargeResult(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21_spec__21(size_t, size_t, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg___lam__0(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Simp_simprocs;
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_Simp_simpMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis_go(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_rewrite_x3f_inErasedSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__2_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasBinderNameHint(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_Simp_dischargeRfl_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dpostDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_seval___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_Simp_sevalGround_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postSEval___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_Simp_dischargeRfl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_Simp_dischargeRfl_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_discharge_x3f_x27___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dpostDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__4___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preSEval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewritePre_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_seval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__2___boxed(lean_object**);
lean_object* l_Lean_Meta_Simp_getSimprocs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_seval___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_synthesizeArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_DischargeResult_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___redArg(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_Simp_sevalGround_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSEvalMethods___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
uint8_t l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_tactic_skipAssignedInstances;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_canUnfoldAtMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkEqTransResultStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preDefault___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_userPostSimprocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preDefault___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_useImplicitDefEqProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___Lean_Meta_Simp_discharge_x3f_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSEvalContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_recordTriedSimpTheorem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Meta_Simp_sevalGround_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isRflTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DischargeResult_noConfusion___redArg___lam__0___boxed(lean_object*);
lean_object* l_Lean_Meta_Simp_getConfig___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewritePost_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_userPreSimprocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_userPreDSimprocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeRfl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_SimprocEntry_try_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postSEval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_getSEvalSimprocs(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instDecidableEqDischargeResult___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSEvalContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpUsingDecide___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_Simp_dischargeRfl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_drewritePost(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___Lean_Meta_Simp_discharge_x3f_x27_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f_spec__2_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_userPostDSimprocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_getMethods(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___Lean_Meta_Simp_discharge_x3f_x27_spec__1___redArg___boxed(lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_recordSimpTheorem___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_discharge_x3f_x27___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertionSort_traverse___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ACLt_main_lt(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_Simp_sevalGround_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preDefault___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_drewritePre_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_Simp_simpMatch_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isDiagnosticsEnabled___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_useImplicitDefEqProof___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_addExtraArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewritePost_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_discharge_x3f_x27___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Simp_Arith_isLinearCnstr(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DischargeResult_noConfusion___redArg___lam__0(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Meta_Simp_sevalGround_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simpMatchCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_synthesizeArgs_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDefaultMethodsCore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DischargeResult_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___Lean_Meta_Simp_discharge_x3f_x27_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DischargeResult_toCtorIdx(uint8_t);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_drewritePost_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchDiscrs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkMethods(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeGround(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedParamInfo;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_discharge_x3f_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_discharge_x3f_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_sevalGround_spec__2(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpUsingDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeRfl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___Lean_Meta_Simp_discharge_x3f_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__2_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preSEval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_isNatExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_recordTheoremWithBadKeys___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkMethods___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDefaultMethods(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_seval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_drewritePre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpUsingDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_Simp_simpMatch_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_List_lengthTR(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dpreDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__2_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DischargeResult_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Meta_Simp_Arith_parentIsTarget(lean_object*, uint8_t);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
uint8_t l_Lean_Meta_Simp_Arith_isLinearTerm(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_Simp_sevalGround_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preSEval___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postSEval___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertionSort_traverse___at___Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpUsingDecide___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_Simp_simpMatch_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DischargeResult_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DischargeResult_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_Simp_DischargeResult_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DischargeResult_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DischargeResult_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_DischargeResult_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DischargeResult_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_DischargeResult_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DischargeResult_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_DischargeResult_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DischargeResult_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_Simp_DischargeResult_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DischargeResult_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Meta_Simp_DischargeResult_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_DischargeResult_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_dec_le(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_eq(x_1, x_2);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(3);
x_12 = lean_unbox(x_11);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(2);
x_14 = lean_unbox(x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_DischargeResult_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Simp_DischargeResult_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_instDecidableEqDischargeResult(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_Simp_DischargeResult_toCtorIdx(x_1);
x_4 = l_Lean_Meta_Simp_DischargeResult_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instDecidableEqDischargeResult___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_Simp_instDecidableEqDischargeResult(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___Lean_Meta_Simp_discharge_x3f_x27_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
x_8 = l_Lean_MessageData_ofConstName(x_3, x_7);
if (x_4 == 0)
{
if (x_5 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_mk_string_unchecked("↓ ", 4, 2);
x_10 = l_Lean_stringToMessageData(x_9);
lean_dec(x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_mk_string_unchecked("", 0, 0);
x_13 = l_Lean_stringToMessageData(x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_mk_string_unchecked("↓ ← ", 8, 4);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
x_19 = lean_mk_string_unchecked("", 0, 0);
x_20 = l_Lean_stringToMessageData(x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_2);
return x_22;
}
}
else
{
if (x_5 == 0)
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_2);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_mk_string_unchecked("← ", 4, 2);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_8);
x_27 = lean_mk_string_unchecked("", 0, 0);
x_28 = l_Lean_stringToMessageData(x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_2);
return x_30;
}
}
}
case 1:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = l_Lean_Expr_fvar___override(x_31);
x_33 = l_Lean_MessageData_ofExpr(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_2);
return x_34;
}
case 2:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_1);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 0);
lean_dec(x_37);
x_38 = l_Lean_MessageData_ofSyntax(x_36);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_38);
return x_1;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
lean_dec(x_1);
x_40 = l_Lean_MessageData_ofSyntax(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_2);
return x_41;
}
}
default: 
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
lean_dec(x_1);
x_43 = l_Lean_MessageData_ofName(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_2);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___Lean_Meta_Simp_discharge_x3f_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_ppOrigin___at___Lean_Meta_Simp_discharge_x3f_x27_spec__0___redArg(x_1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___Lean_Meta_Simp_discharge_x3f_x27_spec__1___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_2 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_box(0);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_4);
x_6 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_7);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___Lean_Meta_Simp_discharge_x3f_x27_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_switch___at___Lean_Meta_Simp_discharge_x3f_x27_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_st_ref_take(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 3);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_12, sizeof(void*)*1);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_unsigned_to_nat(5u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_to_nat(x_16);
x_18 = lean_nat_pow(x_14, x_17);
lean_dec(x_17);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = lean_usize_to_nat(x_19);
x_21 = lean_mk_empty_array_with_capacity(x_20);
lean_dec(x_20);
lean_inc(x_21);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_usize(x_24, 4, x_16);
x_25 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_uint64(x_25, sizeof(void*)*1, x_13);
x_26 = lean_ctor_get(x_7, 4);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 5);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 6);
lean_inc(x_28);
x_29 = lean_ctor_get(x_7, 7);
lean_inc(x_29);
lean_dec(x_7);
x_30 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_30, 0, x_9);
lean_ctor_set(x_30, 1, x_10);
lean_ctor_set(x_30, 2, x_11);
lean_ctor_set(x_30, 3, x_25);
lean_ctor_set(x_30, 4, x_26);
lean_ctor_set(x_30, 5, x_27);
lean_ctor_set(x_30, 6, x_28);
lean_ctor_set(x_30, 7, x_29);
x_31 = lean_st_ref_set(x_1, x_30, x_8);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_4, 3);
lean_inc(x_34);
lean_dec(x_4);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_ctor_get(x_4, 3);
lean_inc(x_37);
lean_dec(x_4);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__2___redArg(x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; lean_object* x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_replaceRef(x_3, x_10);
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
x_17 = lean_ctor_get(x_7, 2);
x_18 = lean_ctor_get(x_7, 3);
x_19 = lean_ctor_get(x_7, 4);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
x_25 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_26 = lean_ctor_get(x_7, 11);
x_27 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_28 = lean_ctor_get(x_7, 12);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_29 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_16);
lean_ctor_set(x_29, 2, x_17);
lean_ctor_set(x_29, 3, x_18);
lean_ctor_set(x_29, 4, x_19);
lean_ctor_set(x_29, 5, x_14);
lean_ctor_set(x_29, 6, x_20);
lean_ctor_set(x_29, 7, x_21);
lean_ctor_set(x_29, 8, x_22);
lean_ctor_set(x_29, 9, x_23);
lean_ctor_set(x_29, 10, x_24);
lean_ctor_set(x_29, 11, x_26);
lean_ctor_set(x_29, 12, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*13, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*13 + 1, x_27);
x_30 = lean_ctor_get(x_12, 3);
lean_inc(x_30);
lean_dec(x_12);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_PersistentArray_toArray___redArg(x_31);
lean_dec(x_31);
x_33 = lean_array_size(x_32);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_usize_of_nat(x_34);
x_36 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21_spec__21(x_33, x_35, x_32);
x_37 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_4);
lean_ctor_set(x_37, 2, x_36);
x_38 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_37, x_5, x_6, x_29, x_8, x_13);
lean_dec(x_29);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_st_ref_take(x_8, x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_43, 3);
lean_inc(x_48);
x_49 = lean_ctor_get_uint64(x_48, sizeof(void*)*1);
lean_dec(x_48);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 0, x_3);
x_50 = l_Lean_PersistentArray_push___redArg(x_1, x_41);
x_51 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set_uint64(x_51, sizeof(void*)*1, x_49);
x_52 = lean_ctor_get(x_43, 4);
lean_inc(x_52);
x_53 = lean_ctor_get(x_43, 5);
lean_inc(x_53);
x_54 = lean_ctor_get(x_43, 6);
lean_inc(x_54);
x_55 = lean_ctor_get(x_43, 7);
lean_inc(x_55);
lean_dec(x_43);
x_56 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_56, 0, x_45);
lean_ctor_set(x_56, 1, x_46);
lean_ctor_set(x_56, 2, x_47);
lean_ctor_set(x_56, 3, x_51);
lean_ctor_set(x_56, 4, x_52);
lean_ctor_set(x_56, 5, x_53);
lean_ctor_set(x_56, 6, x_54);
lean_ctor_set(x_56, 7, x_55);
x_57 = lean_st_ref_set(x_8, x_56, x_44);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
x_60 = lean_box(0);
lean_ctor_set(x_57, 0, x_60);
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec(x_57);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint64_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_64 = lean_ctor_get(x_41, 0);
x_65 = lean_ctor_get(x_41, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_41);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_64, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_64, 3);
lean_inc(x_69);
x_70 = lean_ctor_get_uint64(x_69, sizeof(void*)*1);
lean_dec(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_3);
lean_ctor_set(x_71, 1, x_39);
x_72 = l_Lean_PersistentArray_push___redArg(x_1, x_71);
x_73 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set_uint64(x_73, sizeof(void*)*1, x_70);
x_74 = lean_ctor_get(x_64, 4);
lean_inc(x_74);
x_75 = lean_ctor_get(x_64, 5);
lean_inc(x_75);
x_76 = lean_ctor_get(x_64, 6);
lean_inc(x_76);
x_77 = lean_ctor_get(x_64, 7);
lean_inc(x_77);
lean_dec(x_64);
x_78 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_78, 0, x_66);
lean_ctor_set(x_78, 1, x_67);
lean_ctor_set(x_78, 2, x_68);
lean_ctor_set(x_78, 3, x_73);
lean_ctor_set(x_78, 4, x_74);
lean_ctor_set(x_78, 5, x_75);
lean_ctor_set(x_78, 6, x_76);
lean_ctor_set(x_78, 7, x_77);
x_79 = lean_st_ref_set(x_8, x_78, x_65);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
x_82 = lean_box(0);
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
return x_83;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__3___redArg(x_1, x_2, x_3, x_4, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__4___redArg(x_2, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_io_get_num_heartbeats(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_io_mono_nanos_now(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__3___redArg(x_1, x_5, x_2, x_3, x_10, x_11, x_12, x_13, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__4___redArg(x_4, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; double x_15; double x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_31; lean_object* x_32; double x_33; double x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; double x_57; double x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_84; lean_object* x_85; lean_object* x_86; double x_87; double x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; double x_92; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; double x_102; double x_103; lean_object* x_104; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_203; 
lean_inc(x_1);
x_50 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_1, x_11, x_13);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_96 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg___lam__0), 1, 0);
x_97 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg___lam__1), 1, 0);
x_98 = lean_ctor_get(x_11, 2);
lean_inc(x_98);
x_203 = lean_unbox(x_51);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = l_Lean_trace_profiler;
x_205 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_98, x_204);
if (x_205 == 0)
{
lean_object* x_206; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_206 = lean_apply_8(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_52);
return x_206;
}
else
{
goto block_202;
}
}
else
{
goto block_202;
}
block_30:
{
lean_object* x_22; 
x_22 = lean_unsigned_to_nat(0u);
if (x_17 == 0)
{
double x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_float_of_nat(x_22);
x_24 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_5);
lean_ctor_set_float(x_24, sizeof(void*)*2, x_23);
lean_ctor_set_float(x_24, sizeof(void*)*2 + 8, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 16, x_4);
x_25 = lean_box(0);
x_26 = l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg___lam__2(x_14, x_19, x_20, x_18, x_24, x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_18);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set_float(x_27, sizeof(void*)*2, x_16);
lean_ctor_set_float(x_27, sizeof(void*)*2 + 8, x_15);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 16, x_4);
x_28 = lean_box(0);
x_29 = l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg___lam__2(x_14, x_19, x_20, x_18, x_27, x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_18);
return x_29;
}
}
block_49:
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_11, 5);
lean_inc(x_38);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_39 = lean_apply_9(x_2, x_36, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_35);
if (lean_obj_tag(x_39) == 0)
{
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_14 = x_31;
x_15 = x_34;
x_16 = x_33;
x_17 = x_37;
x_18 = x_32;
x_19 = x_38;
x_20 = x_40;
x_21 = x_41;
goto block_30;
}
else
{
uint8_t x_42; 
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_ctor_set_tag(x_39, 1);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_39);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_dec(x_39);
x_47 = lean_mk_string_unchecked("<exception thrown while producing trace node message>", 53, 53);
x_48 = l_Lean_stringToMessageData(x_47);
lean_dec(x_47);
x_14 = x_31;
x_15 = x_34;
x_16 = x_33;
x_17 = x_37;
x_18 = x_32;
x_19 = x_38;
x_20 = x_48;
x_21 = x_46;
goto block_30;
}
}
block_83:
{
uint8_t x_63; 
x_63 = lean_unbox(x_51);
lean_dec(x_51);
if (x_63 == 0)
{
if (x_62 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint64_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_st_ref_take(x_12, x_61);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc(x_70);
x_71 = lean_ctor_get_uint64(x_70, sizeof(void*)*1);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_PersistentArray_append___redArg(x_56, x_72);
lean_dec(x_72);
x_74 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set_uint64(x_74, sizeof(void*)*1, x_71);
x_75 = lean_ctor_get(x_65, 4);
lean_inc(x_75);
x_76 = lean_ctor_get(x_65, 5);
lean_inc(x_76);
x_77 = lean_ctor_get(x_65, 6);
lean_inc(x_77);
x_78 = lean_ctor_get(x_65, 7);
lean_inc(x_78);
lean_dec(x_65);
x_79 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_79, 0, x_67);
lean_ctor_set(x_79, 1, x_68);
lean_ctor_set(x_79, 2, x_69);
lean_ctor_set(x_79, 3, x_74);
lean_ctor_set(x_79, 4, x_75);
lean_ctor_set(x_79, 5, x_76);
lean_ctor_set(x_79, 6, x_77);
lean_ctor_set(x_79, 7, x_78);
x_80 = lean_st_ref_set(x_12, x_79, x_66);
lean_dec(x_12);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__4___redArg(x_60, x_81);
lean_dec(x_60);
return x_82;
}
else
{
lean_dec(x_56);
x_31 = x_54;
x_32 = x_55;
x_33 = x_57;
x_34 = x_58;
x_35 = x_61;
x_36 = x_60;
x_37 = x_59;
goto block_49;
}
}
else
{
lean_dec(x_56);
x_31 = x_54;
x_32 = x_55;
x_33 = x_57;
x_34 = x_58;
x_35 = x_61;
x_36 = x_60;
x_37 = x_59;
goto block_49;
}
}
block_95:
{
double x_93; uint8_t x_94; 
x_93 = lean_float_sub(x_88, x_87);
x_94 = lean_float_decLt(x_92, x_93);
x_54 = x_84;
x_55 = x_85;
x_56 = x_86;
x_57 = x_87;
x_58 = x_88;
x_59 = x_91;
x_60 = x_90;
x_61 = x_89;
x_62 = x_94;
goto block_83;
}
block_118:
{
lean_object* x_105; uint8_t x_106; 
x_105 = l_Lean_trace_profiler;
x_106 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_98, x_105);
if (x_106 == 0)
{
lean_dec(x_98);
lean_inc(x_101);
x_54 = x_99;
x_55 = x_101;
x_56 = x_100;
x_57 = x_102;
x_58 = x_103;
x_59 = x_106;
x_60 = x_101;
x_61 = x_104;
x_62 = x_106;
goto block_83;
}
else
{
lean_object* x_107; uint8_t x_108; 
x_107 = l_Lean_trace_profiler_useHeartbeats;
x_108 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_98, x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; double x_111; lean_object* x_112; double x_113; double x_114; 
x_109 = l_Lean_trace_profiler_threshold;
x_110 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_98, x_109);
lean_dec(x_98);
x_111 = lean_float_of_nat(x_110);
x_112 = lean_unsigned_to_nat(1000u);
x_113 = lean_float_of_nat(x_112);
x_114 = lean_float_div(x_111, x_113);
lean_inc(x_101);
x_84 = x_99;
x_85 = x_101;
x_86 = x_100;
x_87 = x_102;
x_88 = x_103;
x_89 = x_104;
x_90 = x_101;
x_91 = x_106;
x_92 = x_114;
goto block_95;
}
else
{
lean_object* x_115; lean_object* x_116; double x_117; 
x_115 = l_Lean_trace_profiler_threshold;
x_116 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_98, x_115);
lean_dec(x_98);
x_117 = lean_float_of_nat(x_116);
lean_inc(x_101);
x_84 = x_99;
x_85 = x_101;
x_86 = x_100;
x_87 = x_102;
x_88 = x_103;
x_89 = x_104;
x_90 = x_101;
x_91 = x_106;
x_92 = x_117;
goto block_95;
}
}
}
block_148:
{
lean_object* x_126; 
x_126 = lean_apply_1(x_123, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; double x_129; lean_object* x_130; double x_131; double x_132; double x_133; double x_134; 
lean_dec(x_122);
lean_dec(x_53);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_float_of_nat(x_120);
x_130 = lean_unsigned_to_nat(1000000000u);
x_131 = lean_float_of_nat(x_130);
x_132 = lean_float_div(x_129, x_131);
x_133 = lean_float_of_nat(x_127);
x_134 = lean_float_div(x_133, x_131);
x_99 = x_119;
x_100 = x_121;
x_101 = x_124;
x_102 = x_132;
x_103 = x_134;
x_104 = x_128;
goto block_118;
}
else
{
uint8_t x_135; 
lean_dec(x_124);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_98);
lean_dec(x_51);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_126);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_126, 0);
x_137 = lean_io_error_to_string(x_136);
x_138 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_138, 0, x_137);
x_139 = l_Lean_MessageData_ofFormat(x_138);
if (lean_is_scalar(x_53)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_53;
}
lean_ctor_set(x_140, 0, x_122);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_126, 0, x_140);
return x_126;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_141 = lean_ctor_get(x_126, 0);
x_142 = lean_ctor_get(x_126, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_126);
x_143 = lean_io_error_to_string(x_141);
x_144 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_145 = l_Lean_MessageData_ofFormat(x_144);
if (lean_is_scalar(x_53)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_53;
}
lean_ctor_set(x_146, 0, x_122);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_142);
return x_147;
}
}
}
block_174:
{
lean_object* x_156; 
x_156 = lean_apply_1(x_151, x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; double x_159; double x_160; 
lean_dec(x_153);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_float_of_nat(x_150);
x_160 = lean_float_of_nat(x_157);
x_99 = x_149;
x_100 = x_152;
x_101 = x_154;
x_102 = x_159;
x_103 = x_160;
x_104 = x_158;
goto block_118;
}
else
{
uint8_t x_161; 
lean_dec(x_154);
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_98);
lean_dec(x_51);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_161 = !lean_is_exclusive(x_156);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_162 = lean_ctor_get(x_156, 0);
x_163 = lean_io_error_to_string(x_162);
x_164 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_165 = l_Lean_MessageData_ofFormat(x_164);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_153);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set(x_156, 0, x_166);
return x_156;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_167 = lean_ctor_get(x_156, 0);
x_168 = lean_ctor_get(x_156, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_156);
x_169 = lean_io_error_to_string(x_167);
x_170 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_170, 0, x_169);
x_171 = l_Lean_MessageData_ofFormat(x_170);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_153);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_168);
return x_173;
}
}
}
block_202:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_175 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__2___redArg(x_12, x_52);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = l_Lean_trace_profiler_useHeartbeats;
x_179 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_98, x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_96);
x_180 = lean_ctor_get(x_11, 5);
lean_inc(x_180);
x_181 = l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg___lam__1(x_177);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_184 = lean_apply_8(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_183);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_187, 0, x_185);
lean_inc(x_176);
x_119 = x_176;
x_120 = x_182;
x_121 = x_176;
x_122 = x_180;
x_123 = x_97;
x_124 = x_187;
x_125 = x_186;
goto block_148;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_184, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_184, 1);
lean_inc(x_189);
lean_dec(x_184);
x_190 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_190, 0, x_188);
lean_inc(x_176);
x_119 = x_176;
x_120 = x_182;
x_121 = x_176;
x_122 = x_180;
x_123 = x_97;
x_124 = x_190;
x_125 = x_189;
goto block_148;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_97);
lean_dec(x_53);
x_191 = lean_ctor_get(x_11, 5);
lean_inc(x_191);
x_192 = l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg___lam__0(x_177);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_195 = lean_apply_8(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_194);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_196);
lean_inc(x_176);
x_149 = x_176;
x_150 = x_193;
x_151 = x_96;
x_152 = x_176;
x_153 = x_191;
x_154 = x_198;
x_155 = x_197;
goto block_174;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_195, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_195, 1);
lean_inc(x_200);
lean_dec(x_195);
x_201 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_201, 0, x_199);
lean_inc(x_176);
x_149 = x_176;
x_150 = x_193;
x_151 = x_96;
x_152 = x_176;
x_153 = x_191;
x_154 = x_201;
x_155 = x_200;
goto block_174;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_discharge_x3f_x27___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l_Lean_Meta_ppOrigin___at___Lean_Meta_Simp_discharge_x3f_x27_spec__0___redArg(x_1, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_mk_string_unchecked("", 0, 0);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
lean_inc(x_17);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
x_19 = lean_mk_string_unchecked(" discharge ", 11, 11);
x_20 = l_Lean_stringToMessageData(x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked("❌️", 6, 2);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_17);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
x_26 = l_Lean_indentExpr(x_2);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_17);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_17);
x_29 = l_Lean_Exception_toMessageData(x_12);
x_30 = l_Lean_indentD(x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_17);
lean_ctor_set(x_13, 0, x_32);
return x_13;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = lean_mk_string_unchecked("", 0, 0);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
lean_inc(x_36);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
x_38 = lean_mk_string_unchecked(" discharge ", 11, 11);
x_39 = l_Lean_stringToMessageData(x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_mk_string_unchecked("❌️", 6, 2);
x_42 = l_Lean_stringToMessageData(x_41);
lean_dec(x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
lean_inc(x_36);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_36);
x_45 = l_Lean_indentExpr(x_2);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_inc(x_36);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_36);
x_48 = l_Lean_Exception_toMessageData(x_12);
x_49 = l_Lean_indentD(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_36);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_34);
return x_52;
}
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_3, 0);
lean_inc(x_53);
lean_dec(x_3);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
switch (x_54) {
case 0:
{
lean_object* x_55; uint8_t x_56; 
x_55 = l_Lean_Meta_ppOrigin___at___Lean_Meta_Simp_discharge_x3f_x27_spec__0___redArg(x_1, x_11);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_mk_string_unchecked("", 0, 0);
x_59 = l_Lean_stringToMessageData(x_58);
lean_dec(x_58);
lean_inc(x_59);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
x_61 = lean_mk_string_unchecked(" discharge ", 11, 11);
x_62 = l_Lean_stringToMessageData(x_61);
lean_dec(x_61);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_mk_string_unchecked("✅️", 6, 2);
x_65 = l_Lean_stringToMessageData(x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
lean_inc(x_59);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_59);
x_68 = l_Lean_indentExpr(x_2);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_59);
lean_ctor_set(x_55, 0, x_70);
return x_55;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_71 = lean_ctor_get(x_55, 0);
x_72 = lean_ctor_get(x_55, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_55);
x_73 = lean_mk_string_unchecked("", 0, 0);
x_74 = l_Lean_stringToMessageData(x_73);
lean_dec(x_73);
lean_inc(x_74);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
x_76 = lean_mk_string_unchecked(" discharge ", 11, 11);
x_77 = l_Lean_stringToMessageData(x_76);
lean_dec(x_76);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_mk_string_unchecked("✅️", 6, 2);
x_80 = l_Lean_stringToMessageData(x_79);
lean_dec(x_79);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
lean_inc(x_74);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_74);
x_83 = l_Lean_indentExpr(x_2);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_74);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_72);
return x_86;
}
}
case 1:
{
lean_object* x_87; uint8_t x_88; 
x_87 = l_Lean_Meta_ppOrigin___at___Lean_Meta_Simp_discharge_x3f_x27_spec__0___redArg(x_1, x_11);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_mk_string_unchecked("", 0, 0);
x_91 = l_Lean_stringToMessageData(x_90);
lean_dec(x_90);
lean_inc(x_91);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
x_93 = lean_mk_string_unchecked(" discharge ", 11, 11);
x_94 = l_Lean_stringToMessageData(x_93);
lean_dec(x_93);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_mk_string_unchecked("❌️", 6, 2);
x_97 = l_Lean_stringToMessageData(x_96);
lean_dec(x_96);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_97);
lean_inc(x_91);
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_91);
x_100 = l_Lean_indentExpr(x_2);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_91);
lean_ctor_set(x_87, 0, x_102);
return x_87;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_103 = lean_ctor_get(x_87, 0);
x_104 = lean_ctor_get(x_87, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_87);
x_105 = lean_mk_string_unchecked("", 0, 0);
x_106 = l_Lean_stringToMessageData(x_105);
lean_dec(x_105);
lean_inc(x_106);
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_103);
x_108 = lean_mk_string_unchecked(" discharge ", 11, 11);
x_109 = l_Lean_stringToMessageData(x_108);
lean_dec(x_108);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_mk_string_unchecked("❌️", 6, 2);
x_112 = l_Lean_stringToMessageData(x_111);
lean_dec(x_111);
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_112);
lean_inc(x_106);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_106);
x_115 = l_Lean_indentExpr(x_2);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_106);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_104);
return x_118;
}
}
case 2:
{
lean_object* x_119; uint8_t x_120; 
x_119 = l_Lean_Meta_ppOrigin___at___Lean_Meta_Simp_discharge_x3f_x27_spec__0___redArg(x_1, x_11);
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_121 = lean_ctor_get(x_119, 0);
x_122 = lean_mk_string_unchecked("", 0, 0);
x_123 = l_Lean_stringToMessageData(x_122);
lean_dec(x_122);
lean_inc(x_123);
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
x_125 = lean_mk_string_unchecked(" discharge ", 11, 11);
x_126 = l_Lean_stringToMessageData(x_125);
lean_dec(x_125);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_mk_string_unchecked("❌️", 6, 2);
x_129 = l_Lean_stringToMessageData(x_128);
lean_dec(x_128);
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_mk_string_unchecked(" max depth", 10, 10);
x_132 = l_Lean_stringToMessageData(x_131);
lean_dec(x_131);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_indentExpr(x_2);
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_123);
lean_ctor_set(x_119, 0, x_136);
return x_119;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_137 = lean_ctor_get(x_119, 0);
x_138 = lean_ctor_get(x_119, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_119);
x_139 = lean_mk_string_unchecked("", 0, 0);
x_140 = l_Lean_stringToMessageData(x_139);
lean_dec(x_139);
lean_inc(x_140);
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_137);
x_142 = lean_mk_string_unchecked(" discharge ", 11, 11);
x_143 = l_Lean_stringToMessageData(x_142);
lean_dec(x_142);
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_mk_string_unchecked("❌️", 6, 2);
x_146 = l_Lean_stringToMessageData(x_145);
lean_dec(x_145);
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_mk_string_unchecked(" max depth", 10, 10);
x_149 = l_Lean_stringToMessageData(x_148);
lean_dec(x_148);
x_150 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_149);
x_151 = l_Lean_indentExpr(x_2);
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_140);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_138);
return x_154;
}
}
default: 
{
lean_object* x_155; uint8_t x_156; 
x_155 = l_Lean_Meta_ppOrigin___at___Lean_Meta_Simp_discharge_x3f_x27_spec__0___redArg(x_1, x_11);
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_157 = lean_ctor_get(x_155, 0);
x_158 = lean_mk_string_unchecked("", 0, 0);
x_159 = l_Lean_stringToMessageData(x_158);
lean_dec(x_158);
lean_inc(x_159);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_157);
x_161 = lean_mk_string_unchecked(" discharge ", 11, 11);
x_162 = l_Lean_stringToMessageData(x_161);
lean_dec(x_161);
x_163 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_mk_string_unchecked("❌️", 6, 2);
x_165 = l_Lean_stringToMessageData(x_164);
lean_dec(x_164);
x_166 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_mk_string_unchecked(" failed to assign proof", 23, 23);
x_168 = l_Lean_stringToMessageData(x_167);
lean_dec(x_167);
x_169 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_168);
x_170 = l_Lean_indentExpr(x_2);
x_171 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_159);
lean_ctor_set(x_155, 0, x_172);
return x_155;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_173 = lean_ctor_get(x_155, 0);
x_174 = lean_ctor_get(x_155, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_155);
x_175 = lean_mk_string_unchecked("", 0, 0);
x_176 = l_Lean_stringToMessageData(x_175);
lean_dec(x_175);
lean_inc(x_176);
x_177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_173);
x_178 = lean_mk_string_unchecked(" discharge ", 11, 11);
x_179 = l_Lean_stringToMessageData(x_178);
lean_dec(x_178);
x_180 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_mk_string_unchecked("❌️", 6, 2);
x_182 = l_Lean_stringToMessageData(x_181);
lean_dec(x_181);
x_183 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_mk_string_unchecked(" failed to assign proof", 23, 23);
x_185 = l_Lean_stringToMessageData(x_184);
lean_dec(x_184);
x_186 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_185);
x_187 = l_Lean_indentExpr(x_2);
x_188 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_176);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_174);
return x_190;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_discharge_x3f_x27___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_discharge_x3f_x27___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_ctor_get_uint32(x_4, sizeof(void*)*9);
x_12 = lean_ctor_get_uint32(x_4, sizeof(void*)*9 + 4);
x_13 = lean_uint32_dec_le(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint32_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint32_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_st_ref_get(x_5, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_uint32_of_nat(x_14);
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
x_21 = lean_ctor_get(x_4, 2);
x_22 = lean_ctor_get(x_4, 3);
x_23 = lean_ctor_get(x_4, 4);
x_24 = lean_ctor_get(x_4, 5);
x_25 = lean_ctor_get(x_4, 6);
x_26 = lean_ctor_get(x_4, 7);
x_27 = lean_uint32_add(x_12, x_18);
x_28 = lean_ctor_get(x_4, 8);
x_29 = lean_ctor_get_uint8(x_4, sizeof(void*)*9 + 8);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_30 = lean_alloc_ctor(0, 9, 9);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_20);
lean_ctor_set(x_30, 2, x_21);
lean_ctor_set(x_30, 3, x_22);
lean_ctor_set(x_30, 4, x_23);
lean_ctor_set(x_30, 5, x_24);
lean_ctor_set(x_30, 6, x_25);
lean_ctor_set(x_30, 7, x_26);
lean_ctor_set(x_30, 8, x_28);
lean_ctor_set_uint32(x_30, sizeof(void*)*9, x_11);
lean_ctor_set_uint32(x_30, sizeof(void*)*9 + 4, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*9 + 8, x_29);
lean_inc(x_3);
x_31 = l_Lean_Meta_Simp_getMethods(x_3, x_30, x_5, x_6, x_7, x_8, x_9, x_17);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_5, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_get(x_5, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_st_ref_take(x_5, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = l_Lean_SMap_switch___at___Lean_Meta_Simp_discharge_x3f_x27_spec__1___redArg(x_43);
lean_dec(x_43);
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_41, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_41, 4);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_47);
lean_ctor_set(x_49, 4, x_48);
x_50 = lean_st_ref_set(x_5, x_49, x_42);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_ctor_get(x_35, 0);
lean_inc(x_52);
lean_dec(x_35);
x_53 = lean_ctor_get(x_38, 0);
lean_inc(x_53);
lean_dec(x_38);
x_54 = lean_ctor_get(x_32, 4);
lean_inc(x_54);
lean_dec(x_32);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_ctor_get_uint8(x_53, sizeof(void*)*2);
lean_dec(x_53);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_57 = lean_apply_9(x_54, x_1, x_3, x_30, x_5, x_6, x_7, x_8, x_9, x_51);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_58);
x_61 = l_Lean_Meta_Simp_discharge_x3f_x27___lam__1(x_5, x_56, x_55, x_60, x_59);
lean_dec(x_60);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_ctor_get(x_16, 2);
lean_inc(x_63);
lean_dec(x_16);
x_64 = lean_st_ref_take(x_5, x_62);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 4);
lean_inc(x_70);
lean_dec(x_65);
x_71 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_68);
lean_ctor_set(x_71, 2, x_63);
lean_ctor_set(x_71, 3, x_69);
lean_ctor_set(x_71, 4, x_70);
x_72 = lean_st_ref_set(x_5, x_71, x_66);
lean_dec(x_5);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_72, 0);
lean_dec(x_74);
x_75 = lean_box(1);
lean_ctor_set(x_72, 0, x_75);
return x_72;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec(x_72);
x_77 = lean_box(1);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_61, 1);
lean_inc(x_79);
lean_dec(x_61);
x_80 = lean_ctor_get(x_16, 2);
lean_inc(x_80);
lean_dec(x_16);
x_81 = lean_ctor_get(x_58, 0);
lean_inc(x_81);
lean_dec(x_58);
x_82 = l_Lean_Meta_isExprDefEq(x_2, x_81, x_6, x_7, x_8, x_9, x_79);
lean_dec(x_6);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_st_ref_take(x_5, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_87, 3);
lean_inc(x_91);
x_92 = lean_ctor_get(x_87, 4);
lean_inc(x_92);
lean_dec(x_87);
x_93 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_90);
lean_ctor_set(x_93, 2, x_80);
lean_ctor_set(x_93, 3, x_91);
lean_ctor_set(x_93, 4, x_92);
x_94 = lean_st_ref_set(x_5, x_93, x_88);
lean_dec(x_5);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_94, 0);
lean_dec(x_96);
x_97 = lean_box(3);
lean_ctor_set(x_94, 0, x_97);
return x_94;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
x_99 = lean_box(3);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
uint8_t x_101; 
lean_dec(x_80);
lean_dec(x_5);
x_101 = !lean_is_exclusive(x_82);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_82, 0);
lean_dec(x_102);
x_103 = lean_box(0);
lean_ctor_set(x_82, 0, x_103);
return x_82;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_82, 1);
lean_inc(x_104);
lean_dec(x_82);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_80);
lean_dec(x_5);
x_107 = !lean_is_exclusive(x_82);
if (x_107 == 0)
{
return x_82;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_82, 0);
x_109 = lean_ctor_get(x_82, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_82);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_111 = lean_ctor_get(x_57, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_57, 1);
lean_inc(x_112);
lean_dec(x_57);
x_113 = lean_box(0);
x_114 = l_Lean_Meta_Simp_discharge_x3f_x27___lam__1(x_5, x_56, x_55, x_113, x_112);
lean_dec(x_5);
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_114, 0);
lean_dec(x_116);
lean_ctor_set_tag(x_114, 1);
lean_ctor_set(x_114, 0, x_111);
return x_114;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_111);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = lean_box(2);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_10);
return x_120;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_discharge_x3f_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
lean_inc(x_3);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_discharge_x3f_x27___lam__0___boxed), 11, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_3);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_discharge_x3f_x27___lam__2___boxed), 10, 2);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_2);
x_14 = lean_mk_string_unchecked("Meta", 4, 4);
x_15 = lean_mk_string_unchecked("Tactic", 6, 6);
x_16 = lean_mk_string_unchecked("simp", 4, 4);
x_17 = lean_mk_string_unchecked("discharge", 9, 9);
x_18 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_17);
x_19 = lean_box(1);
x_20 = lean_mk_string_unchecked("", 0, 0);
x_21 = lean_unbox(x_19);
x_22 = l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg(x_18, x_12, x_13, x_21, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_box(0);
x_26 = lean_unbox(x_24);
lean_dec(x_24);
x_27 = lean_unbox(x_25);
x_28 = l_Lean_Meta_Simp_instDecidableEqDischargeResult(x_26, x_27);
x_29 = lean_box(x_28);
lean_ctor_set(x_22, 0, x_29);
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_box(0);
x_33 = lean_unbox(x_30);
lean_dec(x_30);
x_34 = lean_unbox(x_32);
x_35 = l_Lean_Meta_Simp_instDecidableEqDischargeResult(x_33, x_34);
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_22, 0);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_22);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at___Lean_Meta_Simp_discharge_x3f_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_ppOrigin___at___Lean_Meta_Simp_discharge_x3f_x27_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___Lean_Meta_Simp_discharge_x3f_x27_spec__1___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_switch___at___Lean_Meta_Simp_discharge_x3f_x27_spec__1___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___Lean_Meta_Simp_discharge_x3f_x27_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_switch___at___Lean_Meta_Simp_discharge_x3f_x27_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__2___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__4___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_discharge_x3f_x27___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_discharge_x3f_x27___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_discharge_x3f_x27___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Meta_Simp_discharge_x3f_x27___lam__1(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_discharge_x3f_x27___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_discharge_x3f_x27___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_Meta_trySynthInstance(x_3, x_13, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; lean_object* x_113; uint8_t x_114; uint64_t x_115; lean_object* x_116; uint64_t x_117; uint64_t x_118; uint64_t x_119; uint8_t x_120; uint64_t x_121; uint64_t x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; 
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
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_94 = lean_box(3);
x_95 = lean_ctor_get(x_4, 0);
lean_inc(x_95);
x_96 = lean_ctor_get_uint8(x_95, 0);
x_97 = lean_ctor_get_uint8(x_95, 1);
x_98 = lean_ctor_get_uint8(x_95, 2);
x_99 = lean_ctor_get_uint8(x_95, 3);
x_100 = lean_ctor_get_uint8(x_95, 4);
x_101 = lean_ctor_get_uint8(x_95, 5);
x_102 = lean_ctor_get_uint8(x_95, 6);
x_103 = lean_ctor_get_uint8(x_95, 7);
x_104 = lean_ctor_get_uint8(x_95, 8);
x_105 = lean_ctor_get_uint8(x_95, 10);
x_106 = lean_ctor_get_uint8(x_95, 11);
x_107 = lean_ctor_get_uint8(x_95, 12);
x_108 = lean_ctor_get_uint8(x_95, 13);
x_109 = lean_ctor_get_uint8(x_95, 14);
x_110 = lean_ctor_get_uint8(x_95, 15);
x_111 = lean_ctor_get_uint8(x_95, 16);
x_112 = lean_ctor_get_uint8(x_95, 17);
lean_dec(x_95);
x_113 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_113, 0, x_96);
lean_ctor_set_uint8(x_113, 1, x_97);
lean_ctor_set_uint8(x_113, 2, x_98);
lean_ctor_set_uint8(x_113, 3, x_99);
lean_ctor_set_uint8(x_113, 4, x_100);
lean_ctor_set_uint8(x_113, 5, x_101);
lean_ctor_set_uint8(x_113, 6, x_102);
lean_ctor_set_uint8(x_113, 7, x_103);
lean_ctor_set_uint8(x_113, 8, x_104);
x_114 = lean_unbox(x_94);
lean_ctor_set_uint8(x_113, 9, x_114);
lean_ctor_set_uint8(x_113, 10, x_105);
lean_ctor_set_uint8(x_113, 11, x_106);
lean_ctor_set_uint8(x_113, 12, x_107);
lean_ctor_set_uint8(x_113, 13, x_108);
lean_ctor_set_uint8(x_113, 14, x_109);
lean_ctor_set_uint8(x_113, 15, x_110);
lean_ctor_set_uint8(x_113, 16, x_111);
lean_ctor_set_uint8(x_113, 17, x_112);
x_115 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
x_116 = lean_unsigned_to_nat(2u);
x_117 = lean_uint64_of_nat(x_116);
x_118 = lean_uint64_shift_right(x_115, x_117);
x_119 = lean_uint64_shift_left(x_118, x_117);
x_120 = lean_unbox(x_94);
x_121 = l_Lean_Meta_TransparencyMode_toUInt64(x_120);
x_122 = lean_uint64_lor(x_119, x_121);
x_123 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_124 = lean_ctor_get(x_4, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_4, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_4, 3);
lean_inc(x_126);
x_127 = lean_ctor_get(x_4, 4);
lean_inc(x_127);
x_128 = lean_ctor_get(x_4, 5);
lean_inc(x_128);
x_129 = lean_ctor_get(x_4, 6);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_131 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
x_132 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_132, 0, x_113);
lean_ctor_set(x_132, 1, x_124);
lean_ctor_set(x_132, 2, x_125);
lean_ctor_set(x_132, 3, x_126);
lean_ctor_set(x_132, 4, x_127);
lean_ctor_set(x_132, 5, x_128);
lean_ctor_set(x_132, 6, x_129);
lean_ctor_set_uint64(x_132, sizeof(void*)*7, x_122);
lean_ctor_set_uint8(x_132, sizeof(void*)*7 + 8, x_123);
lean_ctor_set_uint8(x_132, sizeof(void*)*7 + 9, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*7 + 10, x_131);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_18);
lean_inc(x_2);
x_133 = l_Lean_Meta_isExprDefEq(x_2, x_18, x_132, x_5, x_6, x_7, x_16);
lean_dec(x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_unbox(x_134);
lean_dec(x_134);
x_19 = x_136;
x_20 = x_135;
goto block_93;
}
else
{
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_133, 1);
lean_inc(x_138);
lean_dec(x_133);
x_139 = lean_unbox(x_137);
lean_dec(x_137);
x_19 = x_139;
x_20 = x_138;
goto block_93;
}
else
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_133;
}
}
block_93:
{
if (x_19 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_17);
x_21 = lean_mk_string_unchecked("Meta", 4, 4);
x_22 = lean_mk_string_unchecked("Tactic", 6, 6);
x_23 = lean_mk_string_unchecked("simp", 4, 4);
x_24 = lean_mk_string_unchecked("discharge", 9, 9);
x_25 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_24);
lean_inc(x_25);
x_26 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_25, x_6, x_20);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = lean_box(x_19);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_box(x_19);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = l_Lean_Meta_ppOrigin___at___Lean_Meta_Simp_discharge_x3f_x27_spec__0___redArg(x_1, x_35);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
x_40 = lean_mk_string_unchecked("", 0, 0);
x_41 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
lean_inc(x_41);
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_38);
lean_ctor_set(x_36, 0, x_41);
x_42 = lean_mk_string_unchecked(", failed to assign instance", 27, 27);
x_43 = l_Lean_stringToMessageData(x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_indentExpr(x_3);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_mk_string_unchecked("\nsythesized value", 17, 17);
x_48 = l_Lean_stringToMessageData(x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_indentExpr(x_18);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_mk_string_unchecked("\nis not definitionally equal to", 31, 31);
x_53 = l_Lean_stringToMessageData(x_52);
lean_dec(x_52);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_indentExpr(x_2);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_41);
x_58 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_25, x_57, x_4, x_5, x_6, x_7, x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
x_61 = lean_box(x_19);
lean_ctor_set(x_58, 0, x_61);
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_box(x_19);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_65 = lean_ctor_get(x_36, 0);
x_66 = lean_ctor_get(x_36, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_36);
x_67 = lean_mk_string_unchecked("", 0, 0);
x_68 = l_Lean_stringToMessageData(x_67);
lean_dec(x_67);
lean_inc(x_68);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_65);
x_70 = lean_mk_string_unchecked(", failed to assign instance", 27, 27);
x_71 = l_Lean_stringToMessageData(x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_indentExpr(x_3);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_mk_string_unchecked("\nsythesized value", 17, 17);
x_76 = l_Lean_stringToMessageData(x_75);
lean_dec(x_75);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_indentExpr(x_18);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_mk_string_unchecked("\nis not definitionally equal to", 31, 31);
x_81 = l_Lean_stringToMessageData(x_80);
lean_dec(x_80);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_indentExpr(x_2);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_68);
x_86 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_25, x_85, x_4, x_5, x_6, x_7, x_66);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
x_89 = lean_box(x_19);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = lean_box(x_19);
if (lean_is_scalar(x_17)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_17;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_20);
return x_92;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_15);
lean_dec(x_2);
x_140 = lean_ctor_get(x_14, 1);
lean_inc(x_140);
lean_dec(x_14);
x_141 = lean_mk_string_unchecked("Meta", 4, 4);
x_142 = lean_mk_string_unchecked("Tactic", 6, 6);
x_143 = lean_mk_string_unchecked("simp", 4, 4);
x_144 = lean_mk_string_unchecked("discharge", 9, 9);
x_145 = l_Lean_Name_mkStr4(x_141, x_142, x_143, x_144);
lean_inc(x_145);
x_146 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_145, x_6, x_140);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_unbox(x_147);
lean_dec(x_147);
if (x_148 == 0)
{
lean_object* x_149; 
lean_dec(x_145);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_dec(x_146);
x_9 = x_149;
goto block_12;
}
else
{
uint8_t x_150; 
x_150 = !lean_is_exclusive(x_146);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_151 = lean_ctor_get(x_146, 1);
x_152 = lean_ctor_get(x_146, 0);
lean_dec(x_152);
x_153 = l_Lean_Meta_ppOrigin___at___Lean_Meta_Simp_discharge_x3f_x27_spec__0___redArg(x_1, x_151);
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_155 = lean_ctor_get(x_153, 0);
x_156 = lean_ctor_get(x_153, 1);
x_157 = lean_mk_string_unchecked("", 0, 0);
x_158 = l_Lean_stringToMessageData(x_157);
lean_dec(x_157);
lean_inc(x_158);
lean_ctor_set_tag(x_153, 7);
lean_ctor_set(x_153, 1, x_155);
lean_ctor_set(x_153, 0, x_158);
x_159 = lean_mk_string_unchecked(", failed to synthesize instance", 31, 31);
x_160 = l_Lean_stringToMessageData(x_159);
lean_dec(x_159);
lean_ctor_set_tag(x_146, 7);
lean_ctor_set(x_146, 1, x_160);
lean_ctor_set(x_146, 0, x_153);
x_161 = l_Lean_indentExpr(x_3);
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_146);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_158);
x_164 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_145, x_163, x_4, x_5, x_6, x_7, x_156);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_9 = x_165;
goto block_12;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_166 = lean_ctor_get(x_153, 0);
x_167 = lean_ctor_get(x_153, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_153);
x_168 = lean_mk_string_unchecked("", 0, 0);
x_169 = l_Lean_stringToMessageData(x_168);
lean_dec(x_168);
lean_inc(x_169);
x_170 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_166);
x_171 = lean_mk_string_unchecked(", failed to synthesize instance", 31, 31);
x_172 = l_Lean_stringToMessageData(x_171);
lean_dec(x_171);
lean_ctor_set_tag(x_146, 7);
lean_ctor_set(x_146, 1, x_172);
lean_ctor_set(x_146, 0, x_170);
x_173 = l_Lean_indentExpr(x_3);
x_174 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_174, 0, x_146);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_169);
x_176 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_145, x_175, x_4, x_5, x_6, x_7, x_167);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_9 = x_177;
goto block_12;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_178 = lean_ctor_get(x_146, 1);
lean_inc(x_178);
lean_dec(x_146);
x_179 = l_Lean_Meta_ppOrigin___at___Lean_Meta_Simp_discharge_x3f_x27_spec__0___redArg(x_1, x_178);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_182 = x_179;
} else {
 lean_dec_ref(x_179);
 x_182 = lean_box(0);
}
x_183 = lean_mk_string_unchecked("", 0, 0);
x_184 = l_Lean_stringToMessageData(x_183);
lean_dec(x_183);
lean_inc(x_184);
if (lean_is_scalar(x_182)) {
 x_185 = lean_alloc_ctor(7, 2, 0);
} else {
 x_185 = x_182;
 lean_ctor_set_tag(x_185, 7);
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_180);
x_186 = lean_mk_string_unchecked(", failed to synthesize instance", 31, 31);
x_187 = l_Lean_stringToMessageData(x_186);
lean_dec(x_186);
x_188 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_187);
x_189 = l_Lean_indentExpr(x_3);
x_190 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_184);
x_192 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_145, x_191, x_4, x_5, x_6, x_7, x_181);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
x_9 = x_193;
goto block_12;
}
}
}
}
else
{
uint8_t x_194; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_194 = !lean_is_exclusive(x_14);
if (x_194 == 0)
{
return x_14;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_14, 0);
x_196 = lean_ctor_get(x_14, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_14);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___redArg(x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0___redArg(x_1, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_synthesizeArgs_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_22; 
x_22 = lean_usize_dec_lt(x_5, x_4);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_14);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_box(0);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_dec(x_6);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 2);
lean_inc(x_27);
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_25);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_14);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_array_uget(x_3, x_5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_31);
x_32 = lean_infer_type(x_31, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_2, 2);
x_36 = l_Lean_Meta_tactic_skipAssignedInstances;
x_37 = lean_unsigned_to_nat(1u);
x_38 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_35, x_36);
x_39 = lean_ctor_get(x_25, 0);
lean_inc(x_39);
lean_dec(x_25);
x_40 = lean_nat_add(x_26, x_37);
lean_inc(x_39);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_27);
if (x_38 == 0)
{
lean_object* x_133; uint8_t x_134; uint8_t x_135; 
x_133 = lean_array_fget(x_39, x_26);
lean_dec(x_26);
lean_dec(x_39);
x_134 = lean_unbox(x_133);
lean_dec(x_133);
x_135 = l_Lean_BinderInfo_isInstImplicit(x_134);
if (x_135 == 0)
{
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_78 = x_7;
x_79 = x_8;
x_80 = x_9;
x_81 = x_10;
x_82 = x_11;
x_83 = x_12;
x_84 = x_13;
x_85 = x_34;
goto block_132;
}
else
{
lean_object* x_136; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_1);
x_136 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___redArg(x_1, x_31, x_33, x_10, x_11, x_12, x_13, x_34);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_unbox(x_137);
if (x_138 == 0)
{
uint8_t x_139; 
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_136);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_136, 0);
lean_dec(x_140);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_137);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_41);
lean_ctor_set(x_136, 0, x_142);
return x_136;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_136, 1);
lean_inc(x_143);
lean_dec(x_136);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_137);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_41);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_143);
return x_146;
}
}
else
{
lean_object* x_147; 
lean_dec(x_137);
x_147 = lean_ctor_get(x_136, 1);
lean_inc(x_147);
lean_dec(x_136);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_78 = x_7;
x_79 = x_8;
x_80 = x_9;
x_81 = x_10;
x_82 = x_11;
x_83 = x_12;
x_84 = x_13;
x_85 = x_147;
goto block_132;
}
}
else
{
uint8_t x_148; 
lean_dec(x_41);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_136);
if (x_148 == 0)
{
return x_136;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_136, 0);
x_150 = lean_ctor_get(x_136, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_136);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
else
{
lean_dec(x_39);
lean_dec(x_26);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_78 = x_7;
x_79 = x_8;
x_80 = x_9;
x_81 = x_10;
x_82 = x_11;
x_83 = x_12;
x_84 = x_13;
x_85 = x_34;
goto block_132;
}
block_77:
{
lean_object* x_50; 
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_33);
x_50 = l_Lean_Meta_isProp(x_33, x_45, x_46, x_47, x_48, x_49);
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
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_33);
lean_dec(x_31);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_24);
lean_ctor_set(x_54, 1, x_41);
x_15 = x_54;
x_16 = x_53;
goto block_21;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_dec(x_50);
lean_inc(x_1);
x_56 = l_Lean_Meta_Simp_discharge_x3f_x27(x_1, x_31, x_33, x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
if (x_58 == 0)
{
uint8_t x_59; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 0);
lean_dec(x_60);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_57);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_41);
lean_ctor_set(x_56, 0, x_62);
return x_56;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_dec(x_56);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_41);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_57);
x_67 = lean_ctor_get(x_56, 1);
lean_inc(x_67);
lean_dec(x_56);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_24);
lean_ctor_set(x_68, 1, x_41);
x_15 = x_68;
x_16 = x_67;
goto block_21;
}
}
else
{
uint8_t x_69; 
lean_dec(x_41);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_56);
if (x_69 == 0)
{
return x_56;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_56, 0);
x_71 = lean_ctor_get(x_56, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_56);
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
uint8_t x_73; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_50);
if (x_73 == 0)
{
return x_50;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_50, 0);
x_75 = lean_ctor_get(x_50, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_50);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
block_132:
{
lean_object* x_86; uint8_t x_87; 
lean_inc(x_31);
x_86 = l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0___redArg(x_31, x_82, x_85);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_86, 0);
x_89 = lean_ctor_get(x_86, 1);
x_90 = l_Lean_Expr_isMVar(x_88);
lean_dec(x_88);
if (x_90 == 0)
{
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_33);
lean_dec(x_31);
lean_ctor_set(x_86, 1, x_41);
lean_ctor_set(x_86, 0, x_24);
x_15 = x_86;
x_16 = x_89;
goto block_21;
}
else
{
lean_object* x_91; 
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_33);
x_91 = l_Lean_Meta_isClass_x3f(x_33, x_81, x_82, x_83, x_84, x_89);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
lean_free_object(x_86);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_42 = x_78;
x_43 = x_79;
x_44 = x_80;
x_45 = x_81;
x_46 = x_82;
x_47 = x_83;
x_48 = x_84;
x_49 = x_93;
goto block_77;
}
else
{
lean_dec(x_92);
if (x_90 == 0)
{
lean_object* x_94; 
lean_free_object(x_86);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_42 = x_78;
x_43 = x_79;
x_44 = x_80;
x_45 = x_81;
x_46 = x_82;
x_47 = x_83;
x_48 = x_84;
x_49 = x_94;
goto block_77;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
lean_dec(x_91);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_1);
x_96 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___redArg(x_1, x_31, x_33, x_81, x_82, x_83, x_84, x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_unbox(x_97);
lean_dec(x_97);
if (x_98 == 0)
{
lean_object* x_99; 
lean_free_object(x_86);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_42 = x_78;
x_43 = x_79;
x_44 = x_80;
x_45 = x_81;
x_46 = x_82;
x_47 = x_83;
x_48 = x_84;
x_49 = x_99;
goto block_77;
}
else
{
lean_object* x_100; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_33);
lean_dec(x_31);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_dec(x_96);
lean_ctor_set(x_86, 1, x_41);
lean_ctor_set(x_86, 0, x_24);
x_15 = x_86;
x_16 = x_100;
goto block_21;
}
}
else
{
uint8_t x_101; 
lean_free_object(x_86);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_41);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_96);
if (x_101 == 0)
{
return x_96;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_96, 0);
x_103 = lean_ctor_get(x_96, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_96);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
}
else
{
uint8_t x_105; 
lean_free_object(x_86);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_41);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_91);
if (x_105 == 0)
{
return x_91;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_91, 0);
x_107 = lean_ctor_get(x_91, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_91);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_ctor_get(x_86, 0);
x_110 = lean_ctor_get(x_86, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_86);
x_111 = l_Lean_Expr_isMVar(x_109);
lean_dec(x_109);
if (x_111 == 0)
{
lean_object* x_112; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_33);
lean_dec(x_31);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_24);
lean_ctor_set(x_112, 1, x_41);
x_15 = x_112;
x_16 = x_110;
goto block_21;
}
else
{
lean_object* x_113; 
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_33);
x_113 = l_Lean_Meta_isClass_x3f(x_33, x_81, x_82, x_83, x_84, x_110);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_42 = x_78;
x_43 = x_79;
x_44 = x_80;
x_45 = x_81;
x_46 = x_82;
x_47 = x_83;
x_48 = x_84;
x_49 = x_115;
goto block_77;
}
else
{
lean_dec(x_114);
if (x_111 == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_42 = x_78;
x_43 = x_79;
x_44 = x_80;
x_45 = x_81;
x_46 = x_82;
x_47 = x_83;
x_48 = x_84;
x_49 = x_116;
goto block_77;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_113, 1);
lean_inc(x_117);
lean_dec(x_113);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_1);
x_118 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___redArg(x_1, x_31, x_33, x_81, x_82, x_83, x_84, x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_unbox(x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_42 = x_78;
x_43 = x_79;
x_44 = x_80;
x_45 = x_81;
x_46 = x_82;
x_47 = x_83;
x_48 = x_84;
x_49 = x_121;
goto block_77;
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_33);
lean_dec(x_31);
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
lean_dec(x_118);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_24);
lean_ctor_set(x_123, 1, x_41);
x_15 = x_123;
x_16 = x_122;
goto block_21;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_41);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_124 = lean_ctor_get(x_118, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_118, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_126 = x_118;
} else {
 lean_dec_ref(x_118);
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
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_41);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_128 = lean_ctor_get(x_113, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_113, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_130 = x_113;
} else {
 lean_dec_ref(x_113);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_32);
if (x_152 == 0)
{
return x_32;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_32, 0);
x_154 = lean_ctor_get(x_32, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_32);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
block_21:
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_5, x_18);
x_5 = x_19;
x_6 = x_15;
x_14 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_2);
x_14 = l_Array_toSubarray___redArg(x_2, x_12, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_array_size(x_3);
x_18 = lean_usize_of_nat(x_12);
lean_inc(x_9);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_synthesizeArgs_spec__1(x_1, x_9, x_3, x_17, x_18, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = lean_box(1);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_box(1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_19, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_30);
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_19);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_synthesizeArgs_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_synthesizeArgs_spec__1(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_synthesizeArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_useImplicitDefEqProof___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_Simp_getConfig___redArg(x_2, x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*2 + 18);
lean_dec(x_9);
x_11 = lean_box(x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*2 + 18);
lean_dec(x_12);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_useImplicitDefEqProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_useImplicitDefEqProof___redArg(x_1, x_3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_useImplicitDefEqProof___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_useImplicitDefEqProof___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_useImplicitDefEqProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_useImplicitDefEqProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_40; 
x_40 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_mk_string_unchecked("", 0, 0);
x_3 = x_41;
goto block_39;
}
else
{
lean_object* x_42; 
x_42 = lean_mk_string_unchecked(":perm", 5, 5);
x_3 = x_42;
goto block_39;
}
block_39:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
x_5 = l_Lean_Meta_ppOrigin___at___Lean_Meta_Simp_discharge_x3f_x27_spec__0___redArg(x_4, x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_mk_string_unchecked(":", 1, 1);
x_9 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l___private_Init_Data_Repr_0__Nat_reprFast(x_10);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_MessageData_ofFormat(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_mk_string_unchecked("", 0, 0);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_3);
x_20 = l_Lean_MessageData_ofFormat(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_5, 0, x_21);
return x_5;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_24 = lean_mk_string_unchecked(":", 1, 1);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = lean_ctor_get(x_1, 3);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l___private_Init_Data_Repr_0__Nat_reprFast(x_26);
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_MessageData_ofFormat(x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked("", 0, 0);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_3);
x_36 = l_Lean_MessageData_ofFormat(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_23);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_ppSimpTheorem___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__0___redArg(x_1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__1___redArg(x_1, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
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
x_47 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_46);
x_48 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_47);
x_49 = l_instInhabitedBool;
x_50 = lean_box(x_49);
x_51 = l_instInhabitedOfMonad___redArg(x_48, x_50);
x_52 = lean_panic_fn(x_51, x_1);
x_53 = lean_apply_8(x_52, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_53;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_6, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
x_16 = l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___redArg(x_15, x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
lean_free_object(x_10);
x_17 = lean_mk_string_unchecked("Lean.MetavarContext", 19, 19);
x_18 = lean_mk_string_unchecked("Lean.isLevelMVarAssignable", 26, 26);
x_19 = lean_unsigned_to_nat(425u);
x_20 = lean_unsigned_to_nat(14u);
x_21 = lean_mk_string_unchecked("unknown universe metavariable", 29, 29);
x_22 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_17, x_18, x_19, x_20, x_21);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
x_23 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2_spec__2_spec__2(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_nat_dec_le(x_25, x_24);
lean_dec(x_24);
lean_dec(x_25);
x_27 = lean_box(x_26);
lean_ctor_set(x_10, 0, x_27);
return x_10;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_10, 0);
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_10);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
x_32 = l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___redArg(x_31, x_1);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_30);
x_33 = lean_mk_string_unchecked("Lean.MetavarContext", 19, 19);
x_34 = lean_mk_string_unchecked("Lean.isLevelMVarAssignable", 26, 26);
x_35 = lean_unsigned_to_nat(425u);
x_36 = lean_unsigned_to_nat(14u);
x_37 = lean_mk_string_unchecked("unknown universe metavariable", 29, 29);
x_38 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_33, x_34, x_35, x_36, x_37);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_33);
x_39 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2_spec__2_spec__2(x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
lean_dec(x_30);
x_42 = lean_nat_dec_le(x_41, x_40);
lean_dec(x_40);
lean_dec(x_41);
x_43 = lean_box(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_29);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_19; 
x_19 = l_Lean_Level_hasMVar(x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(x_19);
lean_inc(x_10);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_10);
x_11 = x_21;
x_12 = x_19;
x_13 = x_10;
goto block_18;
}
else
{
lean_object* x_22; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = lean_unbox(x_23);
lean_dec(x_23);
x_11 = x_22;
x_12 = x_25;
x_13 = x_24;
goto block_18;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_22;
}
}
block_18:
{
if (x_12 == 0)
{
uint8_t x_14; 
lean_dec(x_11);
x_14 = l_Lean_Level_hasMVar(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_17;
}
}
else
{
lean_dec(x_13);
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
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = l_Lean_Level_hasMVar(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
x_1 = x_10;
goto _start;
}
}
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2___lam__0(x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
case 3:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2___lam__0(x_18, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_20;
}
case 5:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2_spec__2(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_22;
}
default: 
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_9);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_1 = x_13;
x_9 = x_17;
goto _start;
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
return x_14;
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
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_21; 
x_21 = l_Lean_Expr_hasMVar(x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(x_21);
lean_inc(x_12);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_12);
x_13 = x_23;
x_14 = x_21;
x_15 = x_12;
goto block_20;
}
else
{
lean_object* x_24; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = lean_unbox(x_25);
lean_dec(x_25);
x_13 = x_24;
x_14 = x_27;
x_15 = x_26;
goto block_20;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_24;
}
}
block_20:
{
if (x_14 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
x_16 = l_Lean_Expr_hasMVar(x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_19;
}
}
else
{
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
x_11 = l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__1___redArg(x_10, x_6, x_9);
lean_dec(x_6);
return x_11;
}
case 3:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
case 4:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 1);
x_15 = l_List_anyM___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__5(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
case 5:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_26; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_26 = l_Lean_Expr_hasMVar(x_16);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(x_26);
lean_inc(x_9);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_9);
x_18 = x_28;
x_19 = x_26;
x_20 = x_9;
goto block_25;
}
else
{
lean_object* x_29; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_29 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
x_32 = lean_unbox(x_30);
lean_dec(x_30);
x_18 = x_29;
x_19 = x_32;
x_20 = x_31;
goto block_25;
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
return x_29;
}
}
block_25:
{
if (x_19 == 0)
{
uint8_t x_21; 
lean_dec(x_18);
x_21 = l_Lean_Expr_hasMVar(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
else
{
x_1 = x_17;
x_9 = x_20;
goto _start;
}
}
else
{
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
}
}
case 6:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_1, 2);
x_36 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_37 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1___lam__0(x_33, x_34, x_35, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_37;
}
case 7:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_1, 0);
x_39 = lean_ctor_get(x_1, 1);
x_40 = lean_ctor_get(x_1, 2);
x_41 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_42 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1___lam__0(x_38, x_39, x_40, x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_42;
}
case 8:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_65; 
x_43 = lean_ctor_get(x_1, 1);
x_44 = lean_ctor_get(x_1, 2);
x_45 = lean_ctor_get(x_1, 3);
x_65 = l_Lean_Expr_hasMVar(x_43);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_box(x_65);
lean_inc(x_9);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_9);
x_54 = x_67;
x_55 = x_65;
x_56 = x_9;
goto block_64;
}
else
{
lean_object* x_68; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_68 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
x_71 = lean_unbox(x_69);
lean_dec(x_69);
x_54 = x_68;
x_55 = x_71;
x_56 = x_70;
goto block_64;
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
return x_68;
}
}
block_53:
{
if (x_47 == 0)
{
uint8_t x_49; 
lean_dec(x_46);
x_49 = l_Lean_Expr_hasMVar(x_45);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
else
{
x_1 = x_45;
x_9 = x_48;
goto _start;
}
}
else
{
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_46;
}
}
block_64:
{
if (x_55 == 0)
{
uint8_t x_57; 
lean_dec(x_54);
x_57 = l_Lean_Expr_hasMVar(x_44);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_box(x_57);
lean_inc(x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
x_46 = x_59;
x_47 = x_57;
x_48 = x_56;
goto block_53;
}
else
{
lean_object* x_60; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_60 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1(x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
x_63 = lean_unbox(x_61);
lean_dec(x_61);
x_46 = x_60;
x_47 = x_63;
x_48 = x_62;
goto block_53;
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
return x_60;
}
}
}
else
{
lean_dec(x_56);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_54;
}
}
}
case 10:
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_1, 1);
x_73 = l_Lean_Expr_hasMVar(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_box(x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_9);
return x_75;
}
else
{
x_1 = x_72;
goto _start;
}
}
case 11:
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_1, 2);
x_78 = l_Lean_Expr_hasMVar(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = lean_box(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_9);
return x_80;
}
else
{
x_1 = x_77;
goto _start;
}
}
default: 
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_9);
return x_83;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_20; lean_object* x_24; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; uint8_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_278; lean_object* x_279; lean_object* x_431; lean_object* x_432; uint64_t x_433; uint8_t x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; uint8_t x_442; lean_object* x_443; lean_object* x_444; 
x_431 = lean_ctor_get(x_9, 3);
lean_inc(x_431);
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get_uint64(x_431, sizeof(void*)*1);
lean_dec(x_431);
x_434 = lean_ctor_get_uint8(x_11, sizeof(void*)*7 + 8);
x_435 = lean_ctor_get(x_11, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_11, 2);
lean_inc(x_436);
x_437 = lean_ctor_get(x_11, 3);
lean_inc(x_437);
x_438 = lean_ctor_get(x_11, 4);
lean_inc(x_438);
x_439 = lean_ctor_get(x_11, 5);
lean_inc(x_439);
x_440 = lean_ctor_get(x_11, 6);
lean_inc(x_440);
x_441 = lean_ctor_get_uint8(x_11, sizeof(void*)*7 + 9);
x_442 = lean_ctor_get_uint8(x_11, sizeof(void*)*7 + 10);
x_443 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_443, 0, x_432);
lean_ctor_set(x_443, 1, x_435);
lean_ctor_set(x_443, 2, x_436);
lean_ctor_set(x_443, 3, x_437);
lean_ctor_set(x_443, 4, x_438);
lean_ctor_set(x_443, 5, x_439);
lean_ctor_set(x_443, 6, x_440);
lean_ctor_set_uint64(x_443, sizeof(void*)*7, x_433);
lean_ctor_set_uint8(x_443, sizeof(void*)*7 + 8, x_434);
lean_ctor_set_uint8(x_443, sizeof(void*)*7 + 9, x_441);
lean_ctor_set_uint8(x_443, sizeof(void*)*7 + 10, x_442);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_7);
lean_inc(x_1);
x_444 = l_Lean_Meta_isExprDefEq(x_1, x_7, x_443, x_12, x_13, x_14, x_15);
lean_dec(x_443);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; lean_object* x_446; uint8_t x_447; 
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_444, 1);
lean_inc(x_446);
lean_dec(x_444);
x_447 = lean_unbox(x_445);
lean_dec(x_445);
x_278 = x_447;
x_279 = x_446;
goto block_430;
}
else
{
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_448; lean_object* x_449; uint8_t x_450; 
x_448 = lean_ctor_get(x_444, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_444, 1);
lean_inc(x_449);
lean_dec(x_444);
x_450 = lean_unbox(x_448);
lean_dec(x_448);
x_278 = x_450;
x_279 = x_449;
goto block_430;
}
else
{
uint8_t x_451; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_451 = !lean_is_exclusive(x_444);
if (x_451 == 0)
{
return x_444;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_452 = lean_ctor_get(x_444, 0);
x_453 = lean_ctor_get(x_444, 1);
lean_inc(x_453);
lean_inc(x_452);
lean_dec(x_444);
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_453);
return x_454;
}
}
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
block_45:
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Meta_Simp_recordSimpTheorem___redArg(x_30, x_32, x_33, x_34, x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_29);
lean_ctor_set_uint8(x_39, sizeof(void*)*2, x_28);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_36, 0, x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_29);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_28);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
block_62:
{
uint8_t x_54; 
x_54 = l_Lean_Expr_hasBinderNameHint(x_5);
lean_dec(x_5);
if (x_54 == 0)
{
x_28 = x_48;
x_29 = x_47;
x_30 = x_49;
x_31 = x_46;
x_32 = x_50;
x_33 = x_51;
x_34 = x_52;
x_35 = x_53;
goto block_45;
}
else
{
lean_object* x_55; 
lean_inc(x_52);
lean_inc(x_51);
x_55 = l_Lean_Expr_resolveBinderNameHint(x_46, x_51, x_52, x_53);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_28 = x_48;
x_29 = x_47;
x_30 = x_49;
x_31 = x_56;
x_32 = x_50;
x_33 = x_51;
x_34 = x_52;
x_35 = x_57;
goto block_45;
}
else
{
uint8_t x_58; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_47);
x_58 = !lean_is_exclusive(x_55);
if (x_58 == 0)
{
return x_55;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_55, 0);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_55);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
block_143:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_dec(x_68);
lean_dec(x_67);
x_75 = lean_mk_string_unchecked("Meta", 4, 4);
x_76 = lean_mk_string_unchecked("Tactic", 6, 6);
x_77 = lean_mk_string_unchecked("simp", 4, 4);
x_78 = lean_mk_string_unchecked("rewrite", 7, 7);
x_79 = l_Lean_Name_mkStr4(x_75, x_76, x_77, x_78);
lean_inc(x_79);
x_80 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_79, x_72, x_74);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; 
lean_dec(x_79);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_7);
lean_dec(x_6);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_46 = x_63;
x_47 = x_65;
x_48 = x_64;
x_49 = x_66;
x_50 = x_69;
x_51 = x_72;
x_52 = x_73;
x_53 = x_83;
goto block_62;
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_80);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_80, 1);
x_86 = lean_ctor_get(x_80, 0);
lean_dec(x_86);
x_87 = l_Lean_Meta_ppSimpTheorem___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__0___redArg(x_6, x_85);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_ctor_get(x_87, 1);
x_91 = lean_mk_string_unchecked("", 0, 0);
x_92 = l_Lean_stringToMessageData(x_91);
lean_dec(x_91);
lean_inc(x_92);
lean_ctor_set_tag(x_87, 7);
lean_ctor_set(x_87, 1, x_89);
lean_ctor_set(x_87, 0, x_92);
x_93 = lean_mk_string_unchecked(":", 1, 1);
x_94 = l_Lean_stringToMessageData(x_93);
lean_dec(x_93);
lean_ctor_set_tag(x_80, 7);
lean_ctor_set(x_80, 1, x_94);
lean_ctor_set(x_80, 0, x_87);
x_95 = l_Lean_indentExpr(x_7);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_80);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_mk_string_unchecked("\n==>", 4, 4);
x_98 = l_Lean_stringToMessageData(x_97);
lean_dec(x_97);
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_98);
lean_inc(x_63);
x_100 = l_Lean_indentExpr(x_63);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_92);
x_103 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_79, x_102, x_70, x_71, x_72, x_73, x_90);
lean_dec(x_71);
lean_dec(x_70);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_46 = x_63;
x_47 = x_65;
x_48 = x_64;
x_49 = x_66;
x_50 = x_69;
x_51 = x_72;
x_52 = x_73;
x_53 = x_104;
goto block_62;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_105 = lean_ctor_get(x_87, 0);
x_106 = lean_ctor_get(x_87, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_87);
x_107 = lean_mk_string_unchecked("", 0, 0);
x_108 = l_Lean_stringToMessageData(x_107);
lean_dec(x_107);
lean_inc(x_108);
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_105);
x_110 = lean_mk_string_unchecked(":", 1, 1);
x_111 = l_Lean_stringToMessageData(x_110);
lean_dec(x_110);
lean_ctor_set_tag(x_80, 7);
lean_ctor_set(x_80, 1, x_111);
lean_ctor_set(x_80, 0, x_109);
x_112 = l_Lean_indentExpr(x_7);
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_80);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_mk_string_unchecked("\n==>", 4, 4);
x_115 = l_Lean_stringToMessageData(x_114);
lean_dec(x_114);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_115);
lean_inc(x_63);
x_117 = l_Lean_indentExpr(x_63);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_108);
x_120 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_79, x_119, x_70, x_71, x_72, x_73, x_106);
lean_dec(x_71);
lean_dec(x_70);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_46 = x_63;
x_47 = x_65;
x_48 = x_64;
x_49 = x_66;
x_50 = x_69;
x_51 = x_72;
x_52 = x_73;
x_53 = x_121;
goto block_62;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_122 = lean_ctor_get(x_80, 1);
lean_inc(x_122);
lean_dec(x_80);
x_123 = l_Lean_Meta_ppSimpTheorem___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__0___redArg(x_6, x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
x_127 = lean_mk_string_unchecked("", 0, 0);
x_128 = l_Lean_stringToMessageData(x_127);
lean_dec(x_127);
lean_inc(x_128);
if (lean_is_scalar(x_126)) {
 x_129 = lean_alloc_ctor(7, 2, 0);
} else {
 x_129 = x_126;
 lean_ctor_set_tag(x_129, 7);
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_124);
x_130 = lean_mk_string_unchecked(":", 1, 1);
x_131 = l_Lean_stringToMessageData(x_130);
lean_dec(x_130);
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_indentExpr(x_7);
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_mk_string_unchecked("\n==>", 4, 4);
x_136 = l_Lean_stringToMessageData(x_135);
lean_dec(x_135);
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_136);
lean_inc(x_63);
x_138 = l_Lean_indentExpr(x_63);
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_128);
x_141 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_79, x_140, x_70, x_71, x_72, x_73, x_125);
lean_dec(x_71);
lean_dec(x_70);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
x_46 = x_63;
x_47 = x_65;
x_48 = x_64;
x_49 = x_66;
x_50 = x_69;
x_51 = x_72;
x_52 = x_73;
x_53 = x_142;
goto block_62;
}
}
}
block_225:
{
if (x_156 == 0)
{
x_63 = x_144;
x_64 = x_150;
x_65 = x_149;
x_66 = x_152;
x_67 = x_155;
x_68 = x_145;
x_69 = x_148;
x_70 = x_146;
x_71 = x_154;
x_72 = x_147;
x_73 = x_151;
x_74 = x_153;
goto block_143;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
lean_dec(x_155);
lean_dec(x_152);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_145);
lean_dec(x_5);
x_157 = lean_mk_string_unchecked("Meta", 4, 4);
x_158 = lean_mk_string_unchecked("Tactic", 6, 6);
x_159 = lean_mk_string_unchecked("simp", 4, 4);
x_160 = lean_mk_string_unchecked("rewrite", 7, 7);
x_161 = l_Lean_Name_mkStr4(x_157, x_158, x_159, x_160);
lean_inc(x_161);
x_162 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_161, x_147, x_153);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_unbox(x_163);
lean_dec(x_163);
if (x_164 == 0)
{
lean_object* x_165; 
lean_dec(x_161);
lean_dec(x_154);
lean_dec(x_151);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_144);
lean_dec(x_7);
lean_dec(x_6);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_20 = x_165;
goto block_23;
}
else
{
uint8_t x_166; 
x_166 = !lean_is_exclusive(x_162);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_167 = lean_ctor_get(x_162, 1);
x_168 = lean_ctor_get(x_162, 0);
lean_dec(x_168);
x_169 = l_Lean_Meta_ppSimpTheorem___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__0___redArg(x_6, x_167);
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_171 = lean_ctor_get(x_169, 0);
x_172 = lean_ctor_get(x_169, 1);
x_173 = lean_mk_string_unchecked("", 0, 0);
x_174 = l_Lean_stringToMessageData(x_173);
lean_dec(x_173);
lean_inc(x_174);
lean_ctor_set_tag(x_169, 7);
lean_ctor_set(x_169, 1, x_171);
lean_ctor_set(x_169, 0, x_174);
x_175 = lean_mk_string_unchecked(", perm rejected ", 16, 16);
x_176 = l_Lean_stringToMessageData(x_175);
lean_dec(x_175);
lean_ctor_set_tag(x_162, 7);
lean_ctor_set(x_162, 1, x_176);
lean_ctor_set(x_162, 0, x_169);
x_177 = l_Lean_MessageData_ofExpr(x_7);
x_178 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_178, 0, x_162);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_mk_string_unchecked(" ==> ", 5, 5);
x_180 = l_Lean_stringToMessageData(x_179);
lean_dec(x_179);
x_181 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_180);
x_182 = l_Lean_MessageData_ofExpr(x_144);
x_183 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_174);
x_185 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_161, x_184, x_146, x_154, x_147, x_151, x_172);
lean_dec(x_151);
lean_dec(x_147);
lean_dec(x_154);
lean_dec(x_146);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
x_20 = x_186;
goto block_23;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_187 = lean_ctor_get(x_169, 0);
x_188 = lean_ctor_get(x_169, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_169);
x_189 = lean_mk_string_unchecked("", 0, 0);
x_190 = l_Lean_stringToMessageData(x_189);
lean_dec(x_189);
lean_inc(x_190);
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_187);
x_192 = lean_mk_string_unchecked(", perm rejected ", 16, 16);
x_193 = l_Lean_stringToMessageData(x_192);
lean_dec(x_192);
lean_ctor_set_tag(x_162, 7);
lean_ctor_set(x_162, 1, x_193);
lean_ctor_set(x_162, 0, x_191);
x_194 = l_Lean_MessageData_ofExpr(x_7);
x_195 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_195, 0, x_162);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_mk_string_unchecked(" ==> ", 5, 5);
x_197 = l_Lean_stringToMessageData(x_196);
lean_dec(x_196);
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_Lean_MessageData_ofExpr(x_144);
x_200 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_190);
x_202 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_161, x_201, x_146, x_154, x_147, x_151, x_188);
lean_dec(x_151);
lean_dec(x_147);
lean_dec(x_154);
lean_dec(x_146);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec(x_202);
x_20 = x_203;
goto block_23;
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_204 = lean_ctor_get(x_162, 1);
lean_inc(x_204);
lean_dec(x_162);
x_205 = l_Lean_Meta_ppSimpTheorem___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__0___redArg(x_6, x_204);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_208 = x_205;
} else {
 lean_dec_ref(x_205);
 x_208 = lean_box(0);
}
x_209 = lean_mk_string_unchecked("", 0, 0);
x_210 = l_Lean_stringToMessageData(x_209);
lean_dec(x_209);
lean_inc(x_210);
if (lean_is_scalar(x_208)) {
 x_211 = lean_alloc_ctor(7, 2, 0);
} else {
 x_211 = x_208;
 lean_ctor_set_tag(x_211, 7);
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_206);
x_212 = lean_mk_string_unchecked(", perm rejected ", 16, 16);
x_213 = l_Lean_stringToMessageData(x_212);
lean_dec(x_212);
x_214 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_213);
x_215 = l_Lean_MessageData_ofExpr(x_7);
x_216 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
x_217 = lean_mk_string_unchecked(" ==> ", 5, 5);
x_218 = l_Lean_stringToMessageData(x_217);
lean_dec(x_217);
x_219 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_218);
x_220 = l_Lean_MessageData_ofExpr(x_144);
x_221 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
x_222 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_210);
x_223 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_161, x_222, x_146, x_154, x_147, x_151, x_207);
lean_dec(x_151);
lean_dec(x_147);
lean_dec(x_154);
lean_dec(x_146);
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
lean_dec(x_223);
x_20 = x_224;
goto block_23;
}
}
}
}
block_277:
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
lean_inc(x_5);
x_237 = l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0___redArg(x_5, x_233, x_236);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
lean_inc(x_7);
x_240 = l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0___redArg(x_7, x_233, x_239);
x_241 = !lean_is_exclusive(x_240);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_242 = lean_ctor_get(x_240, 0);
x_243 = lean_ctor_get(x_240, 1);
x_244 = l_Lean_Expr_appArg_x21(x_238);
lean_dec(x_238);
x_245 = lean_expr_eqv(x_242, x_244);
lean_dec(x_242);
if (x_245 == 0)
{
uint8_t x_246; 
lean_free_object(x_240);
x_246 = lean_ctor_get_uint8(x_6, sizeof(void*)*5 + 1);
if (x_246 == 0)
{
x_63 = x_244;
x_64 = x_226;
x_65 = x_228;
x_66 = x_227;
x_67 = x_229;
x_68 = x_230;
x_69 = x_231;
x_70 = x_232;
x_71 = x_233;
x_72 = x_234;
x_73 = x_235;
x_74 = x_243;
goto block_143;
}
else
{
lean_object* x_247; uint8_t x_248; lean_object* x_249; 
x_247 = lean_box(1);
x_248 = lean_unbox(x_247);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_7);
lean_inc(x_244);
x_249 = l_Lean_Meta_ACLt_main_lt(x_248, x_244, x_7, x_232, x_233, x_234, x_235, x_243);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; uint8_t x_251; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_unbox(x_250);
lean_dec(x_250);
if (x_251 == 0)
{
lean_object* x_252; 
x_252 = lean_ctor_get(x_249, 1);
lean_inc(x_252);
lean_dec(x_249);
x_144 = x_244;
x_145 = x_230;
x_146 = x_232;
x_147 = x_234;
x_148 = x_231;
x_149 = x_228;
x_150 = x_226;
x_151 = x_235;
x_152 = x_227;
x_153 = x_252;
x_154 = x_233;
x_155 = x_229;
x_156 = x_246;
goto block_225;
}
else
{
lean_object* x_253; 
x_253 = lean_ctor_get(x_249, 1);
lean_inc(x_253);
lean_dec(x_249);
x_144 = x_244;
x_145 = x_230;
x_146 = x_232;
x_147 = x_234;
x_148 = x_231;
x_149 = x_228;
x_150 = x_226;
x_151 = x_235;
x_152 = x_227;
x_153 = x_253;
x_154 = x_233;
x_155 = x_229;
x_156 = x_245;
goto block_225;
}
}
else
{
uint8_t x_254; 
lean_dec(x_244);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_254 = !lean_is_exclusive(x_249);
if (x_254 == 0)
{
return x_249;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_249, 0);
x_256 = lean_ctor_get(x_249, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_249);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
}
}
}
else
{
lean_object* x_258; 
lean_dec(x_244);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_258 = lean_box(0);
lean_ctor_set(x_240, 0, x_258);
return x_240;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_259 = lean_ctor_get(x_240, 0);
x_260 = lean_ctor_get(x_240, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_240);
x_261 = l_Lean_Expr_appArg_x21(x_238);
lean_dec(x_238);
x_262 = lean_expr_eqv(x_259, x_261);
lean_dec(x_259);
if (x_262 == 0)
{
uint8_t x_263; 
x_263 = lean_ctor_get_uint8(x_6, sizeof(void*)*5 + 1);
if (x_263 == 0)
{
x_63 = x_261;
x_64 = x_226;
x_65 = x_228;
x_66 = x_227;
x_67 = x_229;
x_68 = x_230;
x_69 = x_231;
x_70 = x_232;
x_71 = x_233;
x_72 = x_234;
x_73 = x_235;
x_74 = x_260;
goto block_143;
}
else
{
lean_object* x_264; uint8_t x_265; lean_object* x_266; 
x_264 = lean_box(1);
x_265 = lean_unbox(x_264);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_7);
lean_inc(x_261);
x_266 = l_Lean_Meta_ACLt_main_lt(x_265, x_261, x_7, x_232, x_233, x_234, x_235, x_260);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; uint8_t x_268; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_unbox(x_267);
lean_dec(x_267);
if (x_268 == 0)
{
lean_object* x_269; 
x_269 = lean_ctor_get(x_266, 1);
lean_inc(x_269);
lean_dec(x_266);
x_144 = x_261;
x_145 = x_230;
x_146 = x_232;
x_147 = x_234;
x_148 = x_231;
x_149 = x_228;
x_150 = x_226;
x_151 = x_235;
x_152 = x_227;
x_153 = x_269;
x_154 = x_233;
x_155 = x_229;
x_156 = x_263;
goto block_225;
}
else
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_266, 1);
lean_inc(x_270);
lean_dec(x_266);
x_144 = x_261;
x_145 = x_230;
x_146 = x_232;
x_147 = x_234;
x_148 = x_231;
x_149 = x_228;
x_150 = x_226;
x_151 = x_235;
x_152 = x_227;
x_153 = x_270;
x_154 = x_233;
x_155 = x_229;
x_156 = x_262;
goto block_225;
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_261);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_271 = lean_ctor_get(x_266, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_266, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_273 = x_266;
} else {
 lean_dec_ref(x_266);
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
}
else
{
lean_object* x_275; lean_object* x_276; 
lean_dec(x_261);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_275 = lean_box(0);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_260);
return x_276;
}
}
}
block_430:
{
if (x_278 == 0)
{
uint8_t x_280; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_280 = l_Lean_Expr_isMVar(x_1);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_281 = lean_mk_string_unchecked("Meta", 4, 4);
x_282 = lean_mk_string_unchecked("Tactic", 6, 6);
x_283 = lean_mk_string_unchecked("simp", 4, 4);
x_284 = lean_mk_string_unchecked("unify", 5, 5);
x_285 = l_Lean_Name_mkStr4(x_281, x_282, x_283, x_284);
lean_inc(x_285);
x_286 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_285, x_13, x_279);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_unbox(x_287);
lean_dec(x_287);
if (x_288 == 0)
{
lean_object* x_289; 
lean_dec(x_285);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_289 = lean_ctor_get(x_286, 1);
lean_inc(x_289);
lean_dec(x_286);
x_16 = x_289;
goto block_19;
}
else
{
uint8_t x_290; 
x_290 = !lean_is_exclusive(x_286);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; 
x_291 = lean_ctor_get(x_286, 1);
x_292 = lean_ctor_get(x_286, 0);
lean_dec(x_292);
x_293 = l_Lean_Meta_ppSimpTheorem___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__0___redArg(x_6, x_291);
x_294 = !lean_is_exclusive(x_293);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_295 = lean_ctor_get(x_293, 0);
x_296 = lean_ctor_get(x_293, 1);
x_297 = lean_mk_string_unchecked("", 0, 0);
x_298 = l_Lean_stringToMessageData(x_297);
lean_dec(x_297);
lean_inc(x_298);
lean_ctor_set_tag(x_293, 7);
lean_ctor_set(x_293, 1, x_295);
lean_ctor_set(x_293, 0, x_298);
x_299 = lean_mk_string_unchecked(", failed to unify", 17, 17);
x_300 = l_Lean_stringToMessageData(x_299);
lean_dec(x_299);
lean_ctor_set_tag(x_286, 7);
lean_ctor_set(x_286, 1, x_300);
lean_ctor_set(x_286, 0, x_293);
x_301 = l_Lean_indentExpr(x_1);
x_302 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_302, 0, x_286);
lean_ctor_set(x_302, 1, x_301);
x_303 = lean_mk_string_unchecked("\nwith", 5, 5);
x_304 = l_Lean_stringToMessageData(x_303);
lean_dec(x_303);
x_305 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_305, 0, x_302);
lean_ctor_set(x_305, 1, x_304);
x_306 = l_Lean_indentExpr(x_7);
x_307 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
x_308 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_298);
x_309 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_285, x_308, x_11, x_12, x_13, x_14, x_296);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_310 = lean_ctor_get(x_309, 1);
lean_inc(x_310);
lean_dec(x_309);
x_16 = x_310;
goto block_19;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_311 = lean_ctor_get(x_293, 0);
x_312 = lean_ctor_get(x_293, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_293);
x_313 = lean_mk_string_unchecked("", 0, 0);
x_314 = l_Lean_stringToMessageData(x_313);
lean_dec(x_313);
lean_inc(x_314);
x_315 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_311);
x_316 = lean_mk_string_unchecked(", failed to unify", 17, 17);
x_317 = l_Lean_stringToMessageData(x_316);
lean_dec(x_316);
lean_ctor_set_tag(x_286, 7);
lean_ctor_set(x_286, 1, x_317);
lean_ctor_set(x_286, 0, x_315);
x_318 = l_Lean_indentExpr(x_1);
x_319 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_319, 0, x_286);
lean_ctor_set(x_319, 1, x_318);
x_320 = lean_mk_string_unchecked("\nwith", 5, 5);
x_321 = l_Lean_stringToMessageData(x_320);
lean_dec(x_320);
x_322 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_322, 0, x_319);
lean_ctor_set(x_322, 1, x_321);
x_323 = l_Lean_indentExpr(x_7);
x_324 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
x_325 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_314);
x_326 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_285, x_325, x_11, x_12, x_13, x_14, x_312);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_327 = lean_ctor_get(x_326, 1);
lean_inc(x_327);
lean_dec(x_326);
x_16 = x_327;
goto block_19;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_328 = lean_ctor_get(x_286, 1);
lean_inc(x_328);
lean_dec(x_286);
x_329 = l_Lean_Meta_ppSimpTheorem___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__0___redArg(x_6, x_328);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_332 = x_329;
} else {
 lean_dec_ref(x_329);
 x_332 = lean_box(0);
}
x_333 = lean_mk_string_unchecked("", 0, 0);
x_334 = l_Lean_stringToMessageData(x_333);
lean_dec(x_333);
lean_inc(x_334);
if (lean_is_scalar(x_332)) {
 x_335 = lean_alloc_ctor(7, 2, 0);
} else {
 x_335 = x_332;
 lean_ctor_set_tag(x_335, 7);
}
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_330);
x_336 = lean_mk_string_unchecked(", failed to unify", 17, 17);
x_337 = l_Lean_stringToMessageData(x_336);
lean_dec(x_336);
x_338 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_337);
x_339 = l_Lean_indentExpr(x_1);
x_340 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
x_341 = lean_mk_string_unchecked("\nwith", 5, 5);
x_342 = l_Lean_stringToMessageData(x_341);
lean_dec(x_341);
x_343 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_343, 0, x_340);
lean_ctor_set(x_343, 1, x_342);
x_344 = l_Lean_indentExpr(x_7);
x_345 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
x_346 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_334);
x_347 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_285, x_346, x_11, x_12, x_13, x_14, x_331);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_348 = lean_ctor_get(x_347, 1);
lean_inc(x_348);
lean_dec(x_347);
x_16 = x_348;
goto block_19;
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_16 = x_279;
goto block_19;
}
}
else
{
lean_object* x_349; lean_object* x_350; 
lean_dec(x_1);
x_349 = lean_ctor_get(x_6, 4);
lean_inc(x_349);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_349);
x_350 = l_Lean_Meta_Simp_synthesizeArgs(x_349, x_3, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_279);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; uint8_t x_352; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_unbox(x_351);
if (x_352 == 0)
{
uint8_t x_353; 
lean_dec(x_351);
lean_dec(x_349);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_353 = !lean_is_exclusive(x_350);
if (x_353 == 0)
{
lean_object* x_354; lean_object* x_355; 
x_354 = lean_ctor_get(x_350, 0);
lean_dec(x_354);
x_355 = lean_box(0);
lean_ctor_set(x_350, 0, x_355);
return x_350;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = lean_ctor_get(x_350, 1);
lean_inc(x_356);
lean_dec(x_350);
x_357 = lean_box(0);
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_356);
return x_358;
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; 
x_359 = lean_ctor_get(x_350, 1);
lean_inc(x_359);
lean_dec(x_350);
x_360 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_useImplicitDefEqProof___redArg(x_6, x_9, x_359);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_unbox(x_361);
lean_dec(x_361);
if (x_362 == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_363 = lean_ctor_get(x_360, 1);
lean_inc(x_363);
lean_dec(x_360);
x_364 = l_Lean_mkAppN(x_4, x_2);
x_365 = l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0___redArg(x_364, x_12, x_363);
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_368 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1(x_366, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_367);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; uint8_t x_370; 
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_unbox(x_369);
lean_dec(x_369);
if (x_370 == 0)
{
lean_object* x_371; lean_object* x_372; uint8_t x_373; 
x_371 = lean_ctor_get(x_368, 1);
lean_inc(x_371);
lean_dec(x_368);
x_372 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_372, 0, x_366);
x_373 = lean_unbox(x_351);
lean_dec(x_351);
x_226 = x_373;
x_227 = x_349;
x_228 = x_372;
x_229 = x_8;
x_230 = x_9;
x_231 = x_10;
x_232 = x_11;
x_233 = x_12;
x_234 = x_13;
x_235 = x_14;
x_236 = x_371;
goto block_277;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; 
lean_dec(x_366);
lean_dec(x_351);
lean_dec(x_349);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_374 = lean_ctor_get(x_368, 1);
lean_inc(x_374);
lean_dec(x_368);
x_375 = lean_mk_string_unchecked("Meta", 4, 4);
x_376 = lean_mk_string_unchecked("Tactic", 6, 6);
x_377 = lean_mk_string_unchecked("simp", 4, 4);
x_378 = lean_mk_string_unchecked("rewrite", 7, 7);
x_379 = l_Lean_Name_mkStr4(x_375, x_376, x_377, x_378);
lean_inc(x_379);
x_380 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_379, x_13, x_374);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_unbox(x_381);
lean_dec(x_381);
if (x_382 == 0)
{
lean_object* x_383; 
lean_dec(x_379);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
x_383 = lean_ctor_get(x_380, 1);
lean_inc(x_383);
lean_dec(x_380);
x_24 = x_383;
goto block_27;
}
else
{
uint8_t x_384; 
x_384 = !lean_is_exclusive(x_380);
if (x_384 == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; 
x_385 = lean_ctor_get(x_380, 1);
x_386 = lean_ctor_get(x_380, 0);
lean_dec(x_386);
x_387 = l_Lean_Meta_ppSimpTheorem___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__0___redArg(x_6, x_385);
x_388 = !lean_is_exclusive(x_387);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_389 = lean_ctor_get(x_387, 0);
x_390 = lean_ctor_get(x_387, 1);
x_391 = lean_mk_string_unchecked("", 0, 0);
x_392 = l_Lean_stringToMessageData(x_391);
lean_dec(x_391);
lean_ctor_set_tag(x_387, 7);
lean_ctor_set(x_387, 1, x_389);
lean_ctor_set(x_387, 0, x_392);
x_393 = lean_mk_string_unchecked(", has unassigned metavariables after unification", 48, 48);
x_394 = l_Lean_stringToMessageData(x_393);
lean_dec(x_393);
lean_ctor_set_tag(x_380, 7);
lean_ctor_set(x_380, 1, x_394);
lean_ctor_set(x_380, 0, x_387);
x_395 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_379, x_380, x_11, x_12, x_13, x_14, x_390);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_396 = lean_ctor_get(x_395, 1);
lean_inc(x_396);
lean_dec(x_395);
x_24 = x_396;
goto block_27;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_397 = lean_ctor_get(x_387, 0);
x_398 = lean_ctor_get(x_387, 1);
lean_inc(x_398);
lean_inc(x_397);
lean_dec(x_387);
x_399 = lean_mk_string_unchecked("", 0, 0);
x_400 = l_Lean_stringToMessageData(x_399);
lean_dec(x_399);
x_401 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_397);
x_402 = lean_mk_string_unchecked(", has unassigned metavariables after unification", 48, 48);
x_403 = l_Lean_stringToMessageData(x_402);
lean_dec(x_402);
lean_ctor_set_tag(x_380, 7);
lean_ctor_set(x_380, 1, x_403);
lean_ctor_set(x_380, 0, x_401);
x_404 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_379, x_380, x_11, x_12, x_13, x_14, x_398);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_405 = lean_ctor_get(x_404, 1);
lean_inc(x_405);
lean_dec(x_404);
x_24 = x_405;
goto block_27;
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_406 = lean_ctor_get(x_380, 1);
lean_inc(x_406);
lean_dec(x_380);
x_407 = l_Lean_Meta_ppSimpTheorem___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__0___redArg(x_6, x_406);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 lean_ctor_release(x_407, 1);
 x_410 = x_407;
} else {
 lean_dec_ref(x_407);
 x_410 = lean_box(0);
}
x_411 = lean_mk_string_unchecked("", 0, 0);
x_412 = l_Lean_stringToMessageData(x_411);
lean_dec(x_411);
if (lean_is_scalar(x_410)) {
 x_413 = lean_alloc_ctor(7, 2, 0);
} else {
 x_413 = x_410;
 lean_ctor_set_tag(x_413, 7);
}
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_408);
x_414 = lean_mk_string_unchecked(", has unassigned metavariables after unification", 48, 48);
x_415 = l_Lean_stringToMessageData(x_414);
lean_dec(x_414);
x_416 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_416, 0, x_413);
lean_ctor_set(x_416, 1, x_415);
x_417 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_379, x_416, x_11, x_12, x_13, x_14, x_409);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
lean_dec(x_417);
x_24 = x_418;
goto block_27;
}
}
}
}
else
{
uint8_t x_419; 
lean_dec(x_366);
lean_dec(x_351);
lean_dec(x_349);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_419 = !lean_is_exclusive(x_368);
if (x_419 == 0)
{
return x_368;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_420 = lean_ctor_get(x_368, 0);
x_421 = lean_ctor_get(x_368, 1);
lean_inc(x_421);
lean_inc(x_420);
lean_dec(x_368);
x_422 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_422, 0, x_420);
lean_ctor_set(x_422, 1, x_421);
return x_422;
}
}
}
else
{
lean_object* x_423; lean_object* x_424; uint8_t x_425; 
lean_dec(x_4);
x_423 = lean_ctor_get(x_360, 1);
lean_inc(x_423);
lean_dec(x_360);
x_424 = lean_box(0);
x_425 = lean_unbox(x_351);
lean_dec(x_351);
x_226 = x_425;
x_227 = x_349;
x_228 = x_424;
x_229 = x_8;
x_230 = x_9;
x_231 = x_10;
x_232 = x_11;
x_233 = x_12;
x_234 = x_13;
x_235 = x_14;
x_236 = x_423;
goto block_277;
}
}
}
else
{
uint8_t x_426; 
lean_dec(x_349);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_426 = !lean_is_exclusive(x_350);
if (x_426 == 0)
{
return x_350;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_350, 0);
x_428 = lean_ctor_get(x_350, 1);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_350);
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
return x_429;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_ppSimpTheorem___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_anyM___at___Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1___lam__0(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_7, 4);
lean_inc(x_21);
x_22 = l_Lean_Meta_Simp_recordTriedSimpTheorem___redArg(x_21, x_11, x_14, x_16);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_22, 1);
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_mk_empty_array_with_capacity(x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_8);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_22, 1, x_27);
lean_ctor_set(x_22, 0, x_6);
x_30 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_SimprocEntry_try_spec__0(x_29, x_22, x_26, lean_box(0), lean_box(0), x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_24);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
x_35 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go(x_1, x_2, x_3, x_4, x_5, x_7, x_33, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
lean_dec(x_34);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_17 = x_37;
goto block_20;
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_42 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1(x_41, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_38);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_7);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = l_Array_reverse(lean_box(0), x_34);
x_47 = l_Lean_Meta_Simp_Result_addExtraArgs(x_40, x_46, x_12, x_13, x_14, x_15, x_45);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_ctor_set(x_36, 0, x_49);
lean_ctor_set(x_47, 0, x_36);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_47, 0);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_47);
lean_ctor_set(x_36, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_36);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_free_object(x_36);
x_53 = !lean_is_exclusive(x_47);
if (x_53 == 0)
{
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_47, 0);
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_47);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_free_object(x_36);
lean_dec(x_40);
lean_dec(x_34);
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
lean_dec(x_42);
x_58 = lean_mk_string_unchecked("Meta", 4, 4);
x_59 = lean_mk_string_unchecked("Tactic", 6, 6);
x_60 = lean_mk_string_unchecked("simp", 4, 4);
x_61 = lean_mk_string_unchecked("rewrite", 7, 7);
x_62 = l_Lean_Name_mkStr4(x_58, x_59, x_60, x_61);
lean_inc(x_62);
x_63 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_62, x_14, x_57);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_62);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_17 = x_66;
goto block_20;
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_63);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_63, 1);
x_69 = lean_ctor_get(x_63, 0);
lean_dec(x_69);
x_70 = l_Lean_Meta_ppSimpTheorem___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__0___redArg(x_7, x_68);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_ctor_get(x_70, 1);
x_74 = lean_mk_string_unchecked("", 0, 0);
x_75 = l_Lean_stringToMessageData(x_74);
lean_dec(x_74);
lean_ctor_set_tag(x_70, 7);
lean_ctor_set(x_70, 1, x_72);
lean_ctor_set(x_70, 0, x_75);
x_76 = lean_mk_string_unchecked(", resulting expression has unassigned metavariables", 51, 51);
x_77 = l_Lean_stringToMessageData(x_76);
lean_dec(x_76);
lean_ctor_set_tag(x_63, 7);
lean_ctor_set(x_63, 1, x_77);
lean_ctor_set(x_63, 0, x_70);
x_78 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_62, x_63, x_12, x_13, x_14, x_15, x_73);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_17 = x_79;
goto block_20;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = lean_ctor_get(x_70, 0);
x_81 = lean_ctor_get(x_70, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_70);
x_82 = lean_mk_string_unchecked("", 0, 0);
x_83 = l_Lean_stringToMessageData(x_82);
lean_dec(x_82);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
x_85 = lean_mk_string_unchecked(", resulting expression has unassigned metavariables", 51, 51);
x_86 = l_Lean_stringToMessageData(x_85);
lean_dec(x_85);
lean_ctor_set_tag(x_63, 7);
lean_ctor_set(x_63, 1, x_86);
lean_ctor_set(x_63, 0, x_84);
x_87 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_62, x_63, x_12, x_13, x_14, x_15, x_81);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_17 = x_88;
goto block_20;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_89 = lean_ctor_get(x_63, 1);
lean_inc(x_89);
lean_dec(x_63);
x_90 = l_Lean_Meta_ppSimpTheorem___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__0___redArg(x_7, x_89);
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
x_94 = lean_mk_string_unchecked("", 0, 0);
x_95 = l_Lean_stringToMessageData(x_94);
lean_dec(x_94);
if (lean_is_scalar(x_93)) {
 x_96 = lean_alloc_ctor(7, 2, 0);
} else {
 x_96 = x_93;
 lean_ctor_set_tag(x_96, 7);
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_91);
x_97 = lean_mk_string_unchecked(", resulting expression has unassigned metavariables", 51, 51);
x_98 = l_Lean_stringToMessageData(x_97);
lean_dec(x_97);
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_62, x_99, x_12, x_13, x_14, x_15, x_92);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_17 = x_101;
goto block_20;
}
}
}
}
else
{
uint8_t x_102; 
lean_free_object(x_36);
lean_dec(x_40);
lean_dec(x_34);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
x_102 = !lean_is_exclusive(x_42);
if (x_102 == 0)
{
return x_42;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_42, 0);
x_104 = lean_ctor_get(x_42, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_42);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_36, 0);
lean_inc(x_106);
lean_dec(x_36);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_108 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1(x_107, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_38);
lean_dec(x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_unbox(x_109);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_7);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_112 = l_Array_reverse(lean_box(0), x_34);
x_113 = l_Lean_Meta_Simp_Result_addExtraArgs(x_106, x_112, x_12, x_13, x_14, x_15, x_111);
lean_dec(x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
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
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_114);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_113, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_113, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_121 = x_113;
} else {
 lean_dec_ref(x_113);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
lean_dec(x_106);
lean_dec(x_34);
x_123 = lean_ctor_get(x_108, 1);
lean_inc(x_123);
lean_dec(x_108);
x_124 = lean_mk_string_unchecked("Meta", 4, 4);
x_125 = lean_mk_string_unchecked("Tactic", 6, 6);
x_126 = lean_mk_string_unchecked("simp", 4, 4);
x_127 = lean_mk_string_unchecked("rewrite", 7, 7);
x_128 = l_Lean_Name_mkStr4(x_124, x_125, x_126, x_127);
lean_inc(x_128);
x_129 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_128, x_14, x_123);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_unbox(x_130);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; 
lean_dec(x_128);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
x_17 = x_132;
goto block_20;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_134 = x_129;
} else {
 lean_dec_ref(x_129);
 x_134 = lean_box(0);
}
x_135 = l_Lean_Meta_ppSimpTheorem___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__0___redArg(x_7, x_133);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_138 = x_135;
} else {
 lean_dec_ref(x_135);
 x_138 = lean_box(0);
}
x_139 = lean_mk_string_unchecked("", 0, 0);
x_140 = l_Lean_stringToMessageData(x_139);
lean_dec(x_139);
if (lean_is_scalar(x_138)) {
 x_141 = lean_alloc_ctor(7, 2, 0);
} else {
 x_141 = x_138;
 lean_ctor_set_tag(x_141, 7);
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_136);
x_142 = lean_mk_string_unchecked(", resulting expression has unassigned metavariables", 51, 51);
x_143 = l_Lean_stringToMessageData(x_142);
lean_dec(x_142);
if (lean_is_scalar(x_134)) {
 x_144 = lean_alloc_ctor(7, 2, 0);
} else {
 x_144 = x_134;
 lean_ctor_set_tag(x_144, 7);
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_143);
x_145 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_128, x_144, x_12, x_13, x_14, x_15, x_137);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_17 = x_146;
goto block_20;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_106);
lean_dec(x_34);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
x_147 = lean_ctor_get(x_108, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_108, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_149 = x_108;
} else {
 lean_dec_ref(x_108);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
}
}
else
{
lean_dec(x_34);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
return x_35;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_151 = lean_ctor_get(x_22, 1);
lean_inc(x_151);
lean_dec(x_22);
x_152 = lean_unsigned_to_nat(0u);
x_153 = lean_mk_empty_array_with_capacity(x_152);
x_154 = lean_unsigned_to_nat(1u);
x_155 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_8);
lean_ctor_set(x_155, 2, x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_6);
lean_ctor_set(x_156, 1, x_153);
x_157 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_SimprocEntry_try_spec__0(x_155, x_156, x_152, lean_box(0), lean_box(0), x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_151);
lean_dec(x_155);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_ctor_get(x_158, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
lean_dec(x_158);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
x_162 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go(x_1, x_2, x_3, x_4, x_5, x_7, x_160, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_159);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; 
lean_dec(x_161);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_17 = x_164;
goto block_20;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_166 = lean_ctor_get(x_163, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 x_167 = x_163;
} else {
 lean_dec_ref(x_163);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_169 = l_Lean_hasAssignableMVar___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__1(x_168, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_165);
lean_dec(x_168);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_unbox(x_170);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_7);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
x_173 = l_Array_reverse(lean_box(0), x_161);
x_174 = l_Lean_Meta_Simp_Result_addExtraArgs(x_166, x_173, x_12, x_13, x_14, x_15, x_172);
lean_dec(x_173);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_177 = x_174;
} else {
 lean_dec_ref(x_174);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_178 = lean_alloc_ctor(1, 1, 0);
} else {
 x_178 = x_167;
}
lean_ctor_set(x_178, 0, x_175);
if (lean_is_scalar(x_177)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_177;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_176);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_167);
x_180 = lean_ctor_get(x_174, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_174, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_182 = x_174;
} else {
 lean_dec_ref(x_174);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_161);
x_184 = lean_ctor_get(x_169, 1);
lean_inc(x_184);
lean_dec(x_169);
x_185 = lean_mk_string_unchecked("Meta", 4, 4);
x_186 = lean_mk_string_unchecked("Tactic", 6, 6);
x_187 = lean_mk_string_unchecked("simp", 4, 4);
x_188 = lean_mk_string_unchecked("rewrite", 7, 7);
x_189 = l_Lean_Name_mkStr4(x_185, x_186, x_187, x_188);
lean_inc(x_189);
x_190 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_189, x_14, x_184);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_unbox(x_191);
lean_dec(x_191);
if (x_192 == 0)
{
lean_object* x_193; 
lean_dec(x_189);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
lean_dec(x_190);
x_17 = x_193;
goto block_20;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_194 = lean_ctor_get(x_190, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_195 = x_190;
} else {
 lean_dec_ref(x_190);
 x_195 = lean_box(0);
}
x_196 = l_Lean_Meta_ppSimpTheorem___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go_spec__0___redArg(x_7, x_194);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_199 = x_196;
} else {
 lean_dec_ref(x_196);
 x_199 = lean_box(0);
}
x_200 = lean_mk_string_unchecked("", 0, 0);
x_201 = l_Lean_stringToMessageData(x_200);
lean_dec(x_200);
if (lean_is_scalar(x_199)) {
 x_202 = lean_alloc_ctor(7, 2, 0);
} else {
 x_202 = x_199;
 lean_ctor_set_tag(x_202, 7);
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_197);
x_203 = lean_mk_string_unchecked(", resulting expression has unassigned metavariables", 51, 51);
x_204 = l_Lean_stringToMessageData(x_203);
lean_dec(x_203);
if (lean_is_scalar(x_195)) {
 x_205 = lean_alloc_ctor(7, 2, 0);
} else {
 x_205 = x_195;
 lean_ctor_set_tag(x_205, 7);
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_204);
x_206 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_189, x_205, x_12, x_13, x_14, x_15, x_198);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec(x_206);
x_17 = x_207;
goto block_20;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_161);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
x_208 = lean_ctor_get(x_169, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_169, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_210 = x_169;
} else {
 lean_dec_ref(x_169);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
}
}
else
{
lean_dec(x_161);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
return x_162;
}
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f_spec__0___redArg___lam__0), 9, 4);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___redArg(x_2, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_1);
x_12 = l_Lean_Meta_SimpTheorem_getValue(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_13);
x_15 = lean_infer_type(x_13, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_Meta_forallMetaTelescopeReducing(x_16, x_18, x_20, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0___redArg(x_27, x_8, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = lean_whnf(x_29, x_7, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Expr_appFn_x21(x_32);
x_35 = l_Lean_Expr_appArg_x21(x_34);
lean_dec(x_34);
x_36 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(x_35, x_25, x_26, x_13, x_32, x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
lean_dec(x_25);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_26);
lean_dec(x_25);
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
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_31);
if (x_37 == 0)
{
return x_31;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_31, 0);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_31);
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
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_21);
if (x_41 == 0)
{
return x_21;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_21, 0);
x_43 = lean_ctor_get(x_21, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_21);
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
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_15);
if (x_45 == 0)
{
return x_15;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_15, 0);
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_15);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_12);
if (x_49 == 0)
{
return x_12;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_12, 0);
x_51 = lean_ctor_get(x_12, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_12);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lam__0), 11, 3);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_3);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f_spec__0___redArg(x_12, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f_spec__0___redArg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f_spec__0(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheorem_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_Meta_SimpTheorem_getValue(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
x_14 = lean_infer_type(x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Meta_forallMetaTelescopeReducing(x_15, x_17, x_19, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0___redArg(x_26, x_7, x_23);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_30 = lean_whnf(x_28, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Expr_appFn_x21(x_31);
x_34 = l_Lean_Expr_appArg_x21(x_33);
lean_dec(x_33);
x_35 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_31);
lean_inc(x_12);
lean_inc(x_25);
lean_inc(x_34);
x_36 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(x_34, x_24, x_25, x_12, x_31, x_2, x_1, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
x_39 = l_Lean_Expr_getAppNumArgs(x_34);
x_40 = l_Lean_Expr_getAppNumArgs(x_2);
x_41 = lean_nat_dec_lt(x_39, x_40);
if (x_41 == 0)
{
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_36;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_36);
x_42 = lean_nat_sub(x_40, x_39);
lean_dec(x_39);
lean_dec(x_40);
x_43 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(x_34, x_24, x_25, x_12, x_31, x_2, x_1, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
lean_dec(x_24);
return x_43;
}
}
else
{
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_36;
}
}
else
{
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_36;
}
}
else
{
uint8_t x_44; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_30);
if (x_44 == 0)
{
return x_30;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_30, 0);
x_46 = lean_ctor_get(x_30, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_30);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_20);
if (x_48 == 0)
{
return x_20;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_20, 0);
x_50 = lean_ctor_get(x_20, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_20);
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
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_14);
if (x_52 == 0)
{
return x_14;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_14, 0);
x_54 = lean_ctor_get(x_14, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_14);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_11);
if (x_56 == 0)
{
return x_11;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_11, 0);
x_58 = lean_ctor_get(x_11, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_11);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheorem_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_tryTheorem_x3f___lam__0), 10, 2);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_1);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f_spec__0___redArg(x_11, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex_unsafe__1(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ptr_addr(x_1);
x_4 = lean_ptr_addr(x_2);
x_5 = lean_usize_dec_eq(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex_unsafe__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex_unsafe__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_rewrite_x3f_inErasedSet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 4);
x_4 = l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0(lean_box(0), x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f_inErasedSet___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Simp_rewrite_x3f_inErasedSet(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = lean_array_fget(x_1, x_2);
x_8 = lean_array_fget(x_1, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_nat_dec_lt(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
if (x_13 == 0)
{
lean_dec(x_6);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_14; 
x_14 = lean_array_fswap(x_1, x_2, x_6);
lean_dec(x_2);
x_1 = x_14;
x_2 = x_6;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f_spec__0_spec__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_traverse___at___Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
lean_inc(x_2);
x_10 = l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f_spec__0_spec__0___redArg(x_1, x_2);
x_11 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_1 = x_10;
x_2 = x_11;
x_3 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f_spec__2_spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_23; 
x_23 = lean_usize_dec_lt(x_6, x_5);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_15);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_37; uint8_t x_90; 
lean_dec(x_7);
x_25 = lean_array_uget(x_4, x_6);
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
x_29 = lean_box(0);
x_30 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
lean_inc(x_2);
x_90 = l_Lean_Meta_Simp_rewrite_x3f_inErasedSet(x_2, x_26);
if (x_90 == 0)
{
if (x_3 == 0)
{
goto block_89;
}
else
{
uint8_t x_91; 
x_91 = lean_ctor_get_uint8(x_26, sizeof(void*)*5 + 2);
if (x_91 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_16 = x_37;
x_17 = x_15;
goto block_22;
}
else
{
if (x_90 == 0)
{
goto block_89;
}
else
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_16 = x_37;
x_17 = x_15;
goto block_22;
}
}
}
}
else
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_16 = x_37;
x_17 = x_15;
goto block_22;
}
block_36:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_31);
if (lean_is_scalar(x_28)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_28;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
block_89:
{
lean_object* x_38; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_38 = l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f(x_1, x_26, x_27, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec(x_28);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_16 = x_37;
x_17 = x_40;
goto block_22;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_37);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
x_43 = lean_mk_string_unchecked("Debug", 5, 5);
x_44 = lean_mk_string_unchecked("Meta", 4, 4);
x_45 = lean_mk_string_unchecked("Tactic", 6, 6);
x_46 = lean_mk_string_unchecked("simp", 4, 4);
x_47 = l_Lean_Name_mkStr4(x_43, x_44, x_45, x_46);
lean_inc(x_47);
x_48 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_47, x_13, x_41);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_47);
lean_dec(x_42);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_31 = x_39;
x_32 = x_51;
goto block_36;
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_53 = lean_ctor_get(x_48, 1);
x_54 = lean_ctor_get(x_48, 0);
lean_dec(x_54);
x_55 = lean_mk_string_unchecked("rewrite result ", 15, 15);
x_56 = l_Lean_stringToMessageData(x_55);
lean_dec(x_55);
x_57 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_48, 7);
lean_ctor_set(x_48, 1, x_57);
lean_ctor_set(x_48, 0, x_56);
x_58 = lean_mk_string_unchecked(" => ", 4, 4);
x_59 = l_Lean_stringToMessageData(x_58);
lean_dec(x_58);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_48);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_ctor_get(x_42, 0);
lean_inc(x_61);
lean_dec(x_42);
x_62 = l_Lean_MessageData_ofExpr(x_61);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_mk_string_unchecked("", 0, 0);
x_65 = l_Lean_stringToMessageData(x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_47, x_66, x_11, x_12, x_13, x_14, x_53);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_31 = x_39;
x_32 = x_68;
goto block_36;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_69 = lean_ctor_get(x_48, 1);
lean_inc(x_69);
lean_dec(x_48);
x_70 = lean_mk_string_unchecked("rewrite result ", 15, 15);
x_71 = l_Lean_stringToMessageData(x_70);
lean_dec(x_70);
x_72 = l_Lean_MessageData_ofExpr(x_1);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_mk_string_unchecked(" => ", 4, 4);
x_75 = l_Lean_stringToMessageData(x_74);
lean_dec(x_74);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_ctor_get(x_42, 0);
lean_inc(x_77);
lean_dec(x_42);
x_78 = l_Lean_MessageData_ofExpr(x_77);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_mk_string_unchecked("", 0, 0);
x_81 = l_Lean_stringToMessageData(x_80);
lean_dec(x_80);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_47, x_82, x_11, x_12, x_13, x_14, x_69);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_31 = x_39;
x_32 = x_84;
goto block_36;
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_37);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_38);
if (x_85 == 0)
{
return x_38;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_38, 0);
x_87 = lean_ctor_get(x_38, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_38);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
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
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f_spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_23; 
x_23 = lean_usize_dec_lt(x_6, x_5);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_15);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_37; uint8_t x_90; 
lean_dec(x_7);
x_25 = lean_array_uget(x_4, x_6);
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
x_29 = lean_box(0);
x_30 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
lean_inc(x_2);
x_90 = l_Lean_Meta_Simp_rewrite_x3f_inErasedSet(x_2, x_26);
if (x_90 == 0)
{
if (x_3 == 0)
{
goto block_89;
}
else
{
uint8_t x_91; 
x_91 = lean_ctor_get_uint8(x_26, sizeof(void*)*5 + 2);
if (x_91 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_16 = x_37;
x_17 = x_15;
goto block_22;
}
else
{
if (x_90 == 0)
{
goto block_89;
}
else
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_16 = x_37;
x_17 = x_15;
goto block_22;
}
}
}
}
else
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_16 = x_37;
x_17 = x_15;
goto block_22;
}
block_36:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_31);
if (lean_is_scalar(x_28)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_28;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
block_89:
{
lean_object* x_38; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_38 = l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f(x_1, x_26, x_27, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec(x_28);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_16 = x_37;
x_17 = x_40;
goto block_22;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_37);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
x_43 = lean_mk_string_unchecked("Debug", 5, 5);
x_44 = lean_mk_string_unchecked("Meta", 4, 4);
x_45 = lean_mk_string_unchecked("Tactic", 6, 6);
x_46 = lean_mk_string_unchecked("simp", 4, 4);
x_47 = l_Lean_Name_mkStr4(x_43, x_44, x_45, x_46);
lean_inc(x_47);
x_48 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_47, x_13, x_41);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_47);
lean_dec(x_42);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_31 = x_39;
x_32 = x_51;
goto block_36;
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_53 = lean_ctor_get(x_48, 1);
x_54 = lean_ctor_get(x_48, 0);
lean_dec(x_54);
x_55 = lean_mk_string_unchecked("rewrite result ", 15, 15);
x_56 = l_Lean_stringToMessageData(x_55);
lean_dec(x_55);
x_57 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_48, 7);
lean_ctor_set(x_48, 1, x_57);
lean_ctor_set(x_48, 0, x_56);
x_58 = lean_mk_string_unchecked(" => ", 4, 4);
x_59 = l_Lean_stringToMessageData(x_58);
lean_dec(x_58);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_48);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_ctor_get(x_42, 0);
lean_inc(x_61);
lean_dec(x_42);
x_62 = l_Lean_MessageData_ofExpr(x_61);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_mk_string_unchecked("", 0, 0);
x_65 = l_Lean_stringToMessageData(x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_47, x_66, x_11, x_12, x_13, x_14, x_53);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_31 = x_39;
x_32 = x_68;
goto block_36;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_69 = lean_ctor_get(x_48, 1);
lean_inc(x_69);
lean_dec(x_48);
x_70 = lean_mk_string_unchecked("rewrite result ", 15, 15);
x_71 = l_Lean_stringToMessageData(x_70);
lean_dec(x_70);
x_72 = l_Lean_MessageData_ofExpr(x_1);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_mk_string_unchecked(" => ", 4, 4);
x_75 = l_Lean_stringToMessageData(x_74);
lean_dec(x_74);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_ctor_get(x_42, 0);
lean_inc(x_77);
lean_dec(x_42);
x_78 = l_Lean_MessageData_ofExpr(x_77);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_mk_string_unchecked("", 0, 0);
x_81 = l_Lean_stringToMessageData(x_80);
lean_dec(x_80);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_47, x_82, x_11, x_12, x_13, x_14, x_69);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_31 = x_39;
x_32 = x_84;
goto block_36;
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_37);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_38);
if (x_85 == 0)
{
return x_38;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_38, 0);
x_87 = lean_ctor_get(x_38, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_38);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
block_22:
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_6, x_19);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_20, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_17);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_89; lean_object* x_90; uint64_t x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; 
x_89 = lean_ctor_get(x_7, 4);
lean_inc(x_89);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get_uint64(x_89, sizeof(void*)*1);
lean_dec(x_89);
x_92 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 8);
x_93 = lean_ctor_get(x_9, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_9, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_9, 3);
lean_inc(x_95);
x_96 = lean_ctor_get(x_9, 4);
lean_inc(x_96);
x_97 = lean_ctor_get(x_9, 5);
lean_inc(x_97);
x_98 = lean_ctor_get(x_9, 6);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 9);
x_100 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 10);
x_101 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_101, 0, x_90);
lean_ctor_set(x_101, 1, x_93);
lean_ctor_set(x_101, 2, x_94);
lean_ctor_set(x_101, 3, x_95);
lean_ctor_set(x_101, 4, x_96);
lean_ctor_set(x_101, 5, x_97);
lean_ctor_set(x_101, 6, x_98);
lean_ctor_set_uint64(x_101, sizeof(void*)*7, x_91);
lean_ctor_set_uint8(x_101, sizeof(void*)*7 + 8, x_92);
lean_ctor_set_uint8(x_101, sizeof(void*)*7 + 9, x_99);
lean_ctor_set_uint8(x_101, sizeof(void*)*7 + 10, x_100);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_102 = l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_box(0), x_2, x_1, x_101, x_10, x_11, x_12, x_13);
lean_dec(x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_18 = x_103;
x_19 = x_104;
goto block_88;
}
else
{
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_102, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_102, 1);
lean_inc(x_106);
lean_dec(x_102);
x_18 = x_105;
x_19 = x_106;
goto block_88;
}
else
{
uint8_t x_107; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_102);
if (x_107 == 0)
{
return x_102;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_102, 0);
x_109 = lean_ctor_get(x_102, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_102);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
block_88:
{
uint8_t x_20; 
x_20 = l_Array_isEmpty___redArg(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get_size(x_18);
x_23 = l_Array_insertionSort_traverse___at___Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f_spec__0(x_18, x_21, x_22);
x_24 = lean_box(0);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_array_size(x_23);
x_28 = lean_usize_of_nat(x_21);
x_29 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f_spec__2(x_1, x_3, x_5, x_23, x_27, x_28, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_23);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_29, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_40);
return x_29;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_29);
if (x_44 == 0)
{
return x_29;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_29, 0);
x_46 = lean_ctor_get(x_29, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_29);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_48 = lean_mk_string_unchecked("Debug", 5, 5);
x_49 = lean_mk_string_unchecked("Meta", 4, 4);
x_50 = lean_mk_string_unchecked("Tactic", 6, 6);
x_51 = lean_mk_string_unchecked("simp", 4, 4);
x_52 = l_Lean_Name_mkStr4(x_48, x_49, x_50, x_51);
lean_inc(x_52);
x_53 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_52, x_11, x_19);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_52);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_14 = x_56;
goto block_17;
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_58 = lean_ctor_get(x_53, 1);
x_59 = lean_ctor_get(x_53, 0);
lean_dec(x_59);
x_60 = lean_mk_string_unchecked("no theorems found for ", 22, 22);
x_61 = l_Lean_stringToMessageData(x_60);
lean_dec(x_60);
x_62 = l_Lean_stringToMessageData(x_4);
lean_ctor_set_tag(x_53, 7);
lean_ctor_set(x_53, 1, x_62);
lean_ctor_set(x_53, 0, x_61);
x_63 = lean_mk_string_unchecked("-rewriting ", 11, 11);
x_64 = l_Lean_stringToMessageData(x_63);
lean_dec(x_63);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_53);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_MessageData_ofExpr(x_1);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_mk_string_unchecked("", 0, 0);
x_69 = l_Lean_stringToMessageData(x_68);
lean_dec(x_68);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_52, x_70, x_9, x_10, x_11, x_12, x_58);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_14 = x_72;
goto block_17;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_73 = lean_ctor_get(x_53, 1);
lean_inc(x_73);
lean_dec(x_53);
x_74 = lean_mk_string_unchecked("no theorems found for ", 22, 22);
x_75 = l_Lean_stringToMessageData(x_74);
lean_dec(x_74);
x_76 = l_Lean_stringToMessageData(x_4);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_mk_string_unchecked("-rewriting ", 11, 11);
x_79 = l_Lean_stringToMessageData(x_78);
lean_dec(x_78);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_MessageData_ofExpr(x_1);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_mk_string_unchecked("", 0, 0);
x_84 = l_Lean_stringToMessageData(x_83);
lean_dec(x_83);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_52, x_85, x_9, x_10, x_11, x_12, x_73);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_14 = x_87;
goto block_17;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f_spec__2_spec__2(x_1, x_2, x_16, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f_spec__2(x_1, x_2, x_16, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_5);
x_9 = lean_array_uget(x_2, x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
x_13 = lean_box(0);
x_14 = l_Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex_unsafe__1(x_1, x_11);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_15 = lean_box(0);
lean_ctor_set(x_9, 1, x_13);
lean_ctor_set(x_9, 0, x_15);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_4, x_17);
x_4 = x_18;
x_5 = x_9;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_9, 1, x_13);
lean_ctor_set(x_9, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_22);
lean_dec(x_9);
x_23 = lean_box(0);
x_24 = l_Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex_unsafe__1(x_1, x_22);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_usize_of_nat(x_27);
x_29 = lean_usize_add(x_4, x_28);
x_4 = x_29;
x_5 = x_26;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_23);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_6);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = l_Lean_isDiagnosticsEnabled___redArg(x_9, x_11);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
uint8_t x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_32, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_32, 0, x_37);
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint64_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_dec(x_32);
x_42 = lean_ctor_get(x_5, 4);
x_43 = lean_ctor_get(x_42, 0);
x_44 = lean_ctor_get_uint64(x_42, sizeof(void*)*1);
x_45 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 8);
x_46 = lean_ctor_get(x_7, 1);
x_47 = lean_ctor_get(x_7, 2);
x_48 = lean_ctor_get(x_7, 3);
x_49 = lean_ctor_get(x_7, 4);
x_50 = lean_ctor_get(x_7, 5);
x_51 = lean_ctor_get(x_7, 6);
x_52 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 9);
x_53 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 10);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_43);
x_54 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_46);
lean_ctor_set(x_54, 2, x_47);
lean_ctor_set(x_54, 3, x_48);
lean_ctor_set(x_54, 4, x_49);
lean_ctor_set(x_54, 5, x_50);
lean_ctor_set(x_54, 6, x_51);
lean_ctor_set_uint64(x_54, sizeof(void*)*7, x_44);
lean_ctor_set_uint8(x_54, sizeof(void*)*7 + 8, x_45);
lean_ctor_set_uint8(x_54, sizeof(void*)*7 + 9, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*7 + 10, x_53);
lean_inc(x_9);
x_55 = l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_box(0), x_2, x_1, x_54, x_8, x_9, x_10, x_41);
lean_dec(x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_12 = x_56;
x_13 = x_57;
goto block_31;
}
else
{
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_dec(x_55);
x_12 = x_58;
x_13 = x_59;
goto block_31;
}
else
{
uint8_t x_60; 
lean_dec(x_9);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
return x_55;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_55, 0);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_55);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
block_31:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_array_size(x_12);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_usize_of_nat(x_18);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex_spec__0___redArg(x_3, x_12, x_17, x_19, x_16, x_13);
lean_dec(x_12);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_Meta_Simp_recordTheoremWithBadKeys___redArg(x_3, x_6, x_9, x_23);
lean_dec(x_9);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_20, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_27);
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex_spec__0___redArg(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex_spec__0(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = lean_array_fget(x_1, x_2);
x_8 = lean_array_fget(x_1, x_6);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 3);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_nat_dec_lt(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_dec(x_6);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_12; 
x_12 = lean_array_fswap(x_1, x_2, x_6);
lean_dec(x_2);
x_1 = x_12;
x_2 = x_6;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__0_spec__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_traverse___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
lean_inc(x_2);
x_10 = l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__0_spec__0___redArg(x_1, x_2);
x_11 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_1 = x_10;
x_2 = x_11;
x_3 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__2_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_1);
x_12 = l_Lean_Meta_SimpTheorem_getValue(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_13);
x_15 = lean_infer_type(x_13, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_Meta_forallMetaTelescopeReducing(x_16, x_18, x_20, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0___redArg(x_27, x_8, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = lean_whnf(x_29, x_7, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Expr_appFn_x21(x_32);
x_35 = l_Lean_Expr_appArg_x21(x_34);
lean_dec(x_34);
x_36 = l_Lean_Expr_getAppNumArgs(x_35);
x_37 = lean_nat_sub(x_2, x_36);
lean_dec(x_36);
x_38 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(x_35, x_25, x_26, x_13, x_32, x_3, x_1, x_37, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
lean_dec(x_25);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
uint8_t x_43; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_21);
if (x_43 == 0)
{
return x_21;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_21, 0);
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_21);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_15);
if (x_47 == 0)
{
return x_15;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_15, 0);
x_49 = lean_ctor_get(x_15, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_15);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_12);
if (x_51 == 0)
{
return x_12;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_12, 0);
x_53 = lean_ctor_get(x_12, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_12);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; uint8_t x_25; 
x_25 = lean_usize_dec_lt(x_8, x_7);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_17);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_54; 
lean_dec(x_9);
x_27 = lean_box(0);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_array_uget(x_6, x_8);
lean_inc(x_4);
x_54 = l_Lean_Meta_Simp_rewrite_x3f_inErasedSet(x_4, x_30);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_30);
x_55 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__2_spec__2___lam__0___boxed), 11, 3);
lean_closure_set(x_55, 0, x_30);
lean_closure_set(x_55, 1, x_1);
lean_closure_set(x_55, 2, x_2);
if (x_5 == 0)
{
x_56 = x_5;
goto block_108;
}
else
{
uint8_t x_109; 
x_109 = lean_ctor_get_uint8(x_30, sizeof(void*)*5 + 2);
if (x_109 == 0)
{
lean_dec(x_55);
lean_dec(x_30);
x_18 = x_29;
x_19 = x_17;
goto block_24;
}
else
{
if (x_54 == 0)
{
x_56 = x_54;
goto block_108;
}
else
{
lean_dec(x_55);
lean_dec(x_30);
x_18 = x_29;
x_19 = x_17;
goto block_24;
}
}
}
block_108:
{
lean_object* x_57; 
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_57 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f_spec__0___redArg(x_55, x_56, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
lean_dec(x_30);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_18 = x_29;
x_19 = x_59;
goto block_24;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_29);
lean_dec(x_4);
lean_dec(x_1);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
x_62 = lean_mk_string_unchecked("Debug", 5, 5);
x_63 = lean_mk_string_unchecked("Meta", 4, 4);
x_64 = lean_mk_string_unchecked("Tactic", 6, 6);
x_65 = lean_mk_string_unchecked("simp", 4, 4);
x_66 = l_Lean_Name_mkStr4(x_62, x_63, x_64, x_65);
lean_inc(x_66);
x_67 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_66, x_15, x_60);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_66);
lean_dec(x_61);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_31 = x_58;
x_32 = x_10;
x_33 = x_11;
x_34 = x_12;
x_35 = x_13;
x_36 = x_14;
x_37 = x_15;
x_38 = x_16;
x_39 = x_70;
goto block_53;
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_67);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_72 = lean_ctor_get(x_67, 1);
x_73 = lean_ctor_get(x_67, 0);
lean_dec(x_73);
x_74 = lean_mk_string_unchecked("rewrite result ", 15, 15);
x_75 = l_Lean_stringToMessageData(x_74);
lean_dec(x_74);
lean_inc(x_2);
x_76 = l_Lean_MessageData_ofExpr(x_2);
lean_ctor_set_tag(x_67, 7);
lean_ctor_set(x_67, 1, x_76);
lean_ctor_set(x_67, 0, x_75);
x_77 = lean_mk_string_unchecked(" => ", 4, 4);
x_78 = l_Lean_stringToMessageData(x_77);
lean_dec(x_77);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_67);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_ctor_get(x_61, 0);
lean_inc(x_80);
lean_dec(x_61);
x_81 = l_Lean_MessageData_ofExpr(x_80);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_mk_string_unchecked("", 0, 0);
x_84 = l_Lean_stringToMessageData(x_83);
lean_dec(x_83);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_66, x_85, x_13, x_14, x_15, x_16, x_72);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_31 = x_58;
x_32 = x_10;
x_33 = x_11;
x_34 = x_12;
x_35 = x_13;
x_36 = x_14;
x_37 = x_15;
x_38 = x_16;
x_39 = x_87;
goto block_53;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_88 = lean_ctor_get(x_67, 1);
lean_inc(x_88);
lean_dec(x_67);
x_89 = lean_mk_string_unchecked("rewrite result ", 15, 15);
x_90 = l_Lean_stringToMessageData(x_89);
lean_dec(x_89);
lean_inc(x_2);
x_91 = l_Lean_MessageData_ofExpr(x_2);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_mk_string_unchecked(" => ", 4, 4);
x_94 = l_Lean_stringToMessageData(x_93);
lean_dec(x_93);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_ctor_get(x_61, 0);
lean_inc(x_96);
lean_dec(x_61);
x_97 = l_Lean_MessageData_ofExpr(x_96);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_mk_string_unchecked("", 0, 0);
x_100 = l_Lean_stringToMessageData(x_99);
lean_dec(x_99);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_66, x_101, x_13, x_14, x_15, x_16, x_88);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_31 = x_58;
x_32 = x_10;
x_33 = x_11;
x_34 = x_12;
x_35 = x_13;
x_36 = x_14;
x_37 = x_15;
x_38 = x_16;
x_39 = x_103;
goto block_53;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_57);
if (x_104 == 0)
{
return x_57;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_57, 0);
x_106 = lean_ctor_get(x_57, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_57);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
else
{
lean_dec(x_30);
x_18 = x_29;
x_19 = x_17;
goto block_24;
}
block_53:
{
lean_object* x_40; 
x_40 = l_Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex(x_2, x_3, x_30, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_31);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_28);
lean_ctor_set(x_40, 0, x_44);
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_dec(x_40);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_31);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_28);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_31);
x_49 = !lean_is_exclusive(x_40);
if (x_49 == 0)
{
return x_40;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_40, 0);
x_51 = lean_ctor_get(x_40, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_40);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
block_24:
{
lean_object* x_20; size_t x_21; size_t x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_add(x_8, x_21);
x_8 = x_22;
x_9 = x_18;
x_17 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; uint8_t x_25; 
x_25 = lean_usize_dec_lt(x_8, x_7);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_17);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_54; 
lean_dec(x_9);
x_27 = lean_box(0);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_array_uget(x_6, x_8);
lean_inc(x_4);
x_54 = l_Lean_Meta_Simp_rewrite_x3f_inErasedSet(x_4, x_30);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_30);
x_55 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__2_spec__2___lam__0___boxed), 11, 3);
lean_closure_set(x_55, 0, x_30);
lean_closure_set(x_55, 1, x_1);
lean_closure_set(x_55, 2, x_2);
if (x_5 == 0)
{
x_56 = x_5;
goto block_108;
}
else
{
uint8_t x_109; 
x_109 = lean_ctor_get_uint8(x_30, sizeof(void*)*5 + 2);
if (x_109 == 0)
{
lean_dec(x_55);
lean_dec(x_30);
x_18 = x_29;
x_19 = x_17;
goto block_24;
}
else
{
if (x_54 == 0)
{
x_56 = x_54;
goto block_108;
}
else
{
lean_dec(x_55);
lean_dec(x_30);
x_18 = x_29;
x_19 = x_17;
goto block_24;
}
}
}
block_108:
{
lean_object* x_57; 
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_57 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f_spec__0___redArg(x_55, x_56, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
lean_dec(x_30);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_18 = x_29;
x_19 = x_59;
goto block_24;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_29);
lean_dec(x_4);
lean_dec(x_1);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
x_62 = lean_mk_string_unchecked("Debug", 5, 5);
x_63 = lean_mk_string_unchecked("Meta", 4, 4);
x_64 = lean_mk_string_unchecked("Tactic", 6, 6);
x_65 = lean_mk_string_unchecked("simp", 4, 4);
x_66 = l_Lean_Name_mkStr4(x_62, x_63, x_64, x_65);
lean_inc(x_66);
x_67 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_66, x_15, x_60);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_66);
lean_dec(x_61);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_31 = x_58;
x_32 = x_10;
x_33 = x_11;
x_34 = x_12;
x_35 = x_13;
x_36 = x_14;
x_37 = x_15;
x_38 = x_16;
x_39 = x_70;
goto block_53;
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_67);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_72 = lean_ctor_get(x_67, 1);
x_73 = lean_ctor_get(x_67, 0);
lean_dec(x_73);
x_74 = lean_mk_string_unchecked("rewrite result ", 15, 15);
x_75 = l_Lean_stringToMessageData(x_74);
lean_dec(x_74);
lean_inc(x_2);
x_76 = l_Lean_MessageData_ofExpr(x_2);
lean_ctor_set_tag(x_67, 7);
lean_ctor_set(x_67, 1, x_76);
lean_ctor_set(x_67, 0, x_75);
x_77 = lean_mk_string_unchecked(" => ", 4, 4);
x_78 = l_Lean_stringToMessageData(x_77);
lean_dec(x_77);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_67);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_ctor_get(x_61, 0);
lean_inc(x_80);
lean_dec(x_61);
x_81 = l_Lean_MessageData_ofExpr(x_80);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_mk_string_unchecked("", 0, 0);
x_84 = l_Lean_stringToMessageData(x_83);
lean_dec(x_83);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_66, x_85, x_13, x_14, x_15, x_16, x_72);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_31 = x_58;
x_32 = x_10;
x_33 = x_11;
x_34 = x_12;
x_35 = x_13;
x_36 = x_14;
x_37 = x_15;
x_38 = x_16;
x_39 = x_87;
goto block_53;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_88 = lean_ctor_get(x_67, 1);
lean_inc(x_88);
lean_dec(x_67);
x_89 = lean_mk_string_unchecked("rewrite result ", 15, 15);
x_90 = l_Lean_stringToMessageData(x_89);
lean_dec(x_89);
lean_inc(x_2);
x_91 = l_Lean_MessageData_ofExpr(x_2);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_mk_string_unchecked(" => ", 4, 4);
x_94 = l_Lean_stringToMessageData(x_93);
lean_dec(x_93);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_ctor_get(x_61, 0);
lean_inc(x_96);
lean_dec(x_61);
x_97 = l_Lean_MessageData_ofExpr(x_96);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_mk_string_unchecked("", 0, 0);
x_100 = l_Lean_stringToMessageData(x_99);
lean_dec(x_99);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_66, x_101, x_13, x_14, x_15, x_16, x_88);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_31 = x_58;
x_32 = x_10;
x_33 = x_11;
x_34 = x_12;
x_35 = x_13;
x_36 = x_14;
x_37 = x_15;
x_38 = x_16;
x_39 = x_103;
goto block_53;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_57);
if (x_104 == 0)
{
return x_57;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_57, 0);
x_106 = lean_ctor_get(x_57, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_57);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
else
{
lean_dec(x_30);
x_18 = x_29;
x_19 = x_17;
goto block_24;
}
block_53:
{
lean_object* x_40; 
x_40 = l_Lean_Meta_Simp_rewrite_x3f_diagnoseWhenNoIndex(x_2, x_3, x_30, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_31);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_28);
lean_ctor_set(x_40, 0, x_44);
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_dec(x_40);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_31);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_28);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_31);
x_49 = !lean_is_exclusive(x_40);
if (x_49 == 0)
{
return x_40;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_40, 0);
x_51 = lean_ctor_get(x_40, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_40);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
block_24:
{
lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_add(x_8, x_21);
x_23 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_22, x_18, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_19);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_140; lean_object* x_141; uint64_t x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; 
x_140 = lean_ctor_get(x_7, 4);
lean_inc(x_140);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get_uint64(x_140, sizeof(void*)*1);
lean_dec(x_140);
x_143 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 8);
x_144 = lean_ctor_get(x_9, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_9, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_9, 3);
lean_inc(x_146);
x_147 = lean_ctor_get(x_9, 4);
lean_inc(x_147);
x_148 = lean_ctor_get(x_9, 5);
lean_inc(x_148);
x_149 = lean_ctor_get(x_9, 6);
lean_inc(x_149);
x_150 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 9);
x_151 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 10);
x_152 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_152, 0, x_141);
lean_ctor_set(x_152, 1, x_144);
lean_ctor_set(x_152, 2, x_145);
lean_ctor_set(x_152, 3, x_146);
lean_ctor_set(x_152, 4, x_147);
lean_ctor_set(x_152, 5, x_148);
lean_ctor_set(x_152, 6, x_149);
lean_ctor_set_uint64(x_152, sizeof(void*)*7, x_142);
lean_ctor_set_uint8(x_152, sizeof(void*)*7 + 8, x_143);
lean_ctor_set_uint8(x_152, sizeof(void*)*7 + 9, x_150);
lean_ctor_set_uint8(x_152, sizeof(void*)*7 + 10, x_151);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_2);
x_153 = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(x_2, x_1, x_152, x_10, x_11, x_12, x_13);
lean_dec(x_152);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_18 = x_154;
x_19 = x_155;
goto block_139;
}
else
{
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_153, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
lean_dec(x_153);
x_18 = x_156;
x_19 = x_157;
goto block_139;
}
else
{
uint8_t x_158; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_153);
if (x_158 == 0)
{
return x_153;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_153, 0);
x_160 = lean_ctor_get(x_153, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_153);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
block_139:
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
x_23 = l_Array_isEmpty___redArg(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_array_get_size(x_21);
x_26 = l_Array_insertionSort_traverse___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__0(x_21, x_24, x_25);
x_27 = lean_box(0);
x_28 = lean_box(0);
lean_ctor_set(x_18, 1, x_28);
lean_ctor_set(x_18, 0, x_27);
x_29 = lean_array_size(x_26);
x_30 = lean_usize_of_nat(x_24);
x_31 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__2(x_22, x_1, x_2, x_3, x_5, x_26, x_29, x_30, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_26);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_31, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_42);
return x_31;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_31, 1);
lean_inc(x_43);
lean_dec(x_31);
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
lean_dec(x_33);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_31);
if (x_46 == 0)
{
return x_31;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_31, 0);
x_48 = lean_ctor_get(x_31, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_31);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_mk_string_unchecked("Debug", 5, 5);
x_51 = lean_mk_string_unchecked("Meta", 4, 4);
x_52 = lean_mk_string_unchecked("Tactic", 6, 6);
x_53 = lean_mk_string_unchecked("simp", 4, 4);
x_54 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_53);
lean_inc(x_54);
x_55 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_54, x_11, x_19);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_54);
lean_free_object(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_14 = x_58;
goto block_17;
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_55);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_60 = lean_ctor_get(x_55, 1);
x_61 = lean_ctor_get(x_55, 0);
lean_dec(x_61);
x_62 = lean_mk_string_unchecked("no theorems found for ", 22, 22);
x_63 = l_Lean_stringToMessageData(x_62);
lean_dec(x_62);
x_64 = l_Lean_stringToMessageData(x_4);
lean_ctor_set_tag(x_55, 7);
lean_ctor_set(x_55, 1, x_64);
lean_ctor_set(x_55, 0, x_63);
x_65 = lean_mk_string_unchecked("-rewriting ", 11, 11);
x_66 = l_Lean_stringToMessageData(x_65);
lean_dec(x_65);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_66);
lean_ctor_set(x_18, 0, x_55);
x_67 = l_Lean_MessageData_ofExpr(x_1);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_18);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_mk_string_unchecked("", 0, 0);
x_70 = l_Lean_stringToMessageData(x_69);
lean_dec(x_69);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_54, x_71, x_9, x_10, x_11, x_12, x_60);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_14 = x_73;
goto block_17;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_74 = lean_ctor_get(x_55, 1);
lean_inc(x_74);
lean_dec(x_55);
x_75 = lean_mk_string_unchecked("no theorems found for ", 22, 22);
x_76 = l_Lean_stringToMessageData(x_75);
lean_dec(x_75);
x_77 = l_Lean_stringToMessageData(x_4);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_mk_string_unchecked("-rewriting ", 11, 11);
x_80 = l_Lean_stringToMessageData(x_79);
lean_dec(x_79);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_80);
lean_ctor_set(x_18, 0, x_78);
x_81 = l_Lean_MessageData_ofExpr(x_1);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_18);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_mk_string_unchecked("", 0, 0);
x_84 = l_Lean_stringToMessageData(x_83);
lean_dec(x_83);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_54, x_85, x_9, x_10, x_11, x_12, x_74);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_14 = x_87;
goto block_17;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_18, 0);
x_89 = lean_ctor_get(x_18, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_18);
x_90 = l_Array_isEmpty___redArg(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; size_t x_97; size_t x_98; lean_object* x_99; 
x_91 = lean_unsigned_to_nat(0u);
x_92 = lean_array_get_size(x_88);
x_93 = l_Array_insertionSort_traverse___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__0(x_88, x_91, x_92);
x_94 = lean_box(0);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_array_size(x_93);
x_98 = lean_usize_of_nat(x_91);
x_99 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__2(x_89, x_1, x_2, x_3, x_5, x_93, x_97, x_98, x_96, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_93);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec(x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_103 = x_99;
} else {
 lean_dec_ref(x_99);
 x_103 = lean_box(0);
}
x_104 = lean_box(0);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_102);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_99, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_107 = x_99;
} else {
 lean_dec_ref(x_99);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_101, 0);
lean_inc(x_108);
lean_dec(x_101);
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_106);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_99, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_99, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_112 = x_99;
} else {
 lean_dec_ref(x_99);
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
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_114 = lean_mk_string_unchecked("Debug", 5, 5);
x_115 = lean_mk_string_unchecked("Meta", 4, 4);
x_116 = lean_mk_string_unchecked("Tactic", 6, 6);
x_117 = lean_mk_string_unchecked("simp", 4, 4);
x_118 = l_Lean_Name_mkStr4(x_114, x_115, x_116, x_117);
lean_inc(x_118);
x_119 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_118, x_11, x_19);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_unbox(x_120);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; 
lean_dec(x_118);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
lean_dec(x_119);
x_14 = x_122;
goto block_17;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_123 = lean_ctor_get(x_119, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_124 = x_119;
} else {
 lean_dec_ref(x_119);
 x_124 = lean_box(0);
}
x_125 = lean_mk_string_unchecked("no theorems found for ", 22, 22);
x_126 = l_Lean_stringToMessageData(x_125);
lean_dec(x_125);
x_127 = l_Lean_stringToMessageData(x_4);
if (lean_is_scalar(x_124)) {
 x_128 = lean_alloc_ctor(7, 2, 0);
} else {
 x_128 = x_124;
 lean_ctor_set_tag(x_128, 7);
}
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_mk_string_unchecked("-rewriting ", 11, 11);
x_130 = l_Lean_stringToMessageData(x_129);
lean_dec(x_129);
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lean_MessageData_ofExpr(x_1);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_mk_string_unchecked("", 0, 0);
x_135 = l_Lean_stringToMessageData(x_134);
lean_dec(x_134);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_118, x_136, x_9, x_10, x_11, x_12, x_123);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec(x_137);
x_14 = x_138;
goto block_17;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__2_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__2_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__2_spec__2___boxed(lean_object** _args) {
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
uint8_t x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_unbox(x_5);
lean_dec(x_5);
x_19 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_20 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__2_spec__2(x_1, x_2, x_3, x_4, x_18, x_6, x_19, x_20, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_6);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__2___boxed(lean_object** _args) {
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
uint8_t x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_unbox(x_5);
lean_dec(x_5);
x_19 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_20 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f_spec__2(x_1, x_2, x_3, x_4, x_18, x_6, x_19, x_20, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_6);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Meta_Simp_getConfig___redArg(x_7, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*2 + 17);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Meta_Simp_rewrite_x3f_rewriteNoIndex_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l_Lean_Meta_Simp_rewrite_x3f_rewriteUsingIndex_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_Simp_rewrite_x3f(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpUsingDecide___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_29; uint8_t x_30; 
x_21 = l_Lean_Meta_Simp_getConfig___redArg(x_2, x_7);
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
x_29 = lean_ctor_get_uint8(x_22, sizeof(void*)*2 + 9);
lean_dec(x_22);
if (x_29 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_259 = lean_box(0);
x_260 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_260, 0, x_259);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_23);
return x_261;
}
else
{
uint8_t x_262; 
x_262 = l_Lean_Expr_hasFVar(x_1);
if (x_262 == 0)
{
uint8_t x_263; 
x_263 = l_Lean_Expr_hasMVar(x_1);
x_30 = x_263;
goto block_258;
}
else
{
x_30 = x_262;
goto block_258;
}
}
block_14:
{
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_dec(x_8);
return x_9;
}
}
block_20:
{
uint8_t x_18; 
x_18 = l_Lean_Exception_isInterrupt(x_16);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Exception_isRuntime(x_16);
lean_dec(x_16);
x_8 = x_17;
x_9 = x_15;
x_10 = x_19;
goto block_14;
}
else
{
lean_dec(x_16);
x_8 = x_17;
x_9 = x_15;
x_10 = x_18;
goto block_14;
}
}
block_28:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
if (lean_is_scalar(x_24)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_24;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
block_258:
{
if (x_30 == 0)
{
uint8_t x_31; 
lean_inc(x_1);
x_31 = l_Lean_Expr_isTrue(x_1);
if (x_31 == 0)
{
uint8_t x_32; 
lean_inc(x_1);
x_32 = l_Lean_Expr_isFalse(x_1);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_24);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_33 = l_Lean_Meta_mkDecide(x_1, x_3, x_4, x_5, x_6, x_23);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; uint8_t x_56; uint64_t x_57; lean_object* x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; uint8_t x_62; uint64_t x_63; uint64_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_box(1);
x_37 = lean_ctor_get(x_3, 0);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_37, 0);
x_39 = lean_ctor_get_uint8(x_37, 1);
x_40 = lean_ctor_get_uint8(x_37, 2);
x_41 = lean_ctor_get_uint8(x_37, 3);
x_42 = lean_ctor_get_uint8(x_37, 4);
x_43 = lean_ctor_get_uint8(x_37, 5);
x_44 = lean_ctor_get_uint8(x_37, 6);
x_45 = lean_ctor_get_uint8(x_37, 7);
x_46 = lean_ctor_get_uint8(x_37, 8);
x_47 = lean_ctor_get_uint8(x_37, 10);
x_48 = lean_ctor_get_uint8(x_37, 11);
x_49 = lean_ctor_get_uint8(x_37, 12);
x_50 = lean_ctor_get_uint8(x_37, 13);
x_51 = lean_ctor_get_uint8(x_37, 14);
x_52 = lean_ctor_get_uint8(x_37, 15);
x_53 = lean_ctor_get_uint8(x_37, 16);
x_54 = lean_ctor_get_uint8(x_37, 17);
lean_dec(x_37);
x_55 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_55, 0, x_38);
lean_ctor_set_uint8(x_55, 1, x_39);
lean_ctor_set_uint8(x_55, 2, x_40);
lean_ctor_set_uint8(x_55, 3, x_41);
lean_ctor_set_uint8(x_55, 4, x_42);
lean_ctor_set_uint8(x_55, 5, x_43);
lean_ctor_set_uint8(x_55, 6, x_44);
lean_ctor_set_uint8(x_55, 7, x_45);
lean_ctor_set_uint8(x_55, 8, x_46);
x_56 = lean_unbox(x_36);
lean_ctor_set_uint8(x_55, 9, x_56);
lean_ctor_set_uint8(x_55, 10, x_47);
lean_ctor_set_uint8(x_55, 11, x_48);
lean_ctor_set_uint8(x_55, 12, x_49);
lean_ctor_set_uint8(x_55, 13, x_50);
lean_ctor_set_uint8(x_55, 14, x_51);
lean_ctor_set_uint8(x_55, 15, x_52);
lean_ctor_set_uint8(x_55, 16, x_53);
lean_ctor_set_uint8(x_55, 17, x_54);
x_57 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_58 = lean_unsigned_to_nat(2u);
x_59 = lean_uint64_of_nat(x_58);
x_60 = lean_uint64_shift_right(x_57, x_59);
x_61 = lean_uint64_shift_left(x_60, x_59);
x_62 = lean_unbox(x_36);
x_63 = l_Lean_Meta_TransparencyMode_toUInt64(x_62);
x_64 = lean_uint64_lor(x_61, x_63);
x_65 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_66 = lean_ctor_get(x_3, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_3, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_3, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_3, 4);
lean_inc(x_69);
x_70 = lean_ctor_get(x_3, 5);
lean_inc(x_70);
x_71 = lean_ctor_get(x_3, 6);
lean_inc(x_71);
x_72 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_73 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
x_74 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_74, 0, x_55);
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_34);
x_75 = lean_whnf(x_34, x_74, x_4, x_5, x_6, x_35);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
x_79 = lean_mk_string_unchecked("Bool", 4, 4);
x_80 = lean_mk_string_unchecked("true", 4, 4);
lean_inc(x_79);
x_81 = l_Lean_Name_mkStr2(x_79, x_80);
x_82 = l_Lean_Expr_isConstOf(x_77, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
lean_dec(x_81);
x_83 = lean_mk_string_unchecked("false", 5, 5);
x_84 = l_Lean_Name_mkStr2(x_79, x_83);
x_85 = l_Lean_Expr_isConstOf(x_77, x_84);
lean_dec(x_77);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_84);
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_75, 0, x_87);
return x_75;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_free_object(x_75);
x_88 = lean_box(0);
x_89 = l_Lean_Expr_const___override(x_84, x_88);
x_90 = l_Lean_Meta_mkEqRefl(x_89, x_3, x_4, x_5, x_6, x_78);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_mk_string_unchecked("False", 5, 5);
x_94 = l_Lean_Name_mkStr1(x_93);
x_95 = l_Lean_Expr_const___override(x_94, x_88);
x_96 = lean_mk_string_unchecked("eq_false_of_decide", 18, 18);
x_97 = l_Lean_Name_mkStr1(x_96);
x_98 = l_Lean_Expr_const___override(x_97, x_88);
x_99 = l_Lean_Expr_appArg_x21(x_34);
lean_dec(x_34);
x_100 = lean_unsigned_to_nat(3u);
x_101 = lean_mk_empty_array_with_capacity(x_100);
x_102 = lean_array_push(x_101, x_1);
x_103 = lean_array_push(x_102, x_99);
x_104 = lean_array_push(x_103, x_92);
x_105 = l_Lean_mkAppN(x_98, x_104);
lean_dec(x_104);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_107, 0, x_95);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set_uint8(x_107, sizeof(void*)*2, x_29);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_90, 0, x_108);
return x_90;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_109 = lean_ctor_get(x_90, 0);
x_110 = lean_ctor_get(x_90, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_90);
x_111 = lean_mk_string_unchecked("False", 5, 5);
x_112 = l_Lean_Name_mkStr1(x_111);
x_113 = l_Lean_Expr_const___override(x_112, x_88);
x_114 = lean_mk_string_unchecked("eq_false_of_decide", 18, 18);
x_115 = l_Lean_Name_mkStr1(x_114);
x_116 = l_Lean_Expr_const___override(x_115, x_88);
x_117 = l_Lean_Expr_appArg_x21(x_34);
lean_dec(x_34);
x_118 = lean_unsigned_to_nat(3u);
x_119 = lean_mk_empty_array_with_capacity(x_118);
x_120 = lean_array_push(x_119, x_1);
x_121 = lean_array_push(x_120, x_117);
x_122 = lean_array_push(x_121, x_109);
x_123 = l_Lean_mkAppN(x_116, x_122);
lean_dec(x_122);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_125, 0, x_113);
lean_ctor_set(x_125, 1, x_124);
lean_ctor_set_uint8(x_125, sizeof(void*)*2, x_29);
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_110);
return x_127;
}
}
else
{
uint8_t x_128; 
lean_dec(x_34);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_90);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_90, 0);
x_130 = lean_ctor_get(x_90, 1);
lean_inc(x_130);
lean_inc(x_129);
x_15 = x_90;
x_16 = x_129;
x_17 = x_130;
goto block_20;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_90, 0);
x_132 = lean_ctor_get(x_90, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_90);
lean_inc(x_132);
lean_inc(x_131);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_15 = x_133;
x_16 = x_131;
x_17 = x_132;
goto block_20;
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_79);
lean_free_object(x_75);
lean_dec(x_77);
x_134 = lean_box(0);
x_135 = l_Lean_Expr_const___override(x_81, x_134);
x_136 = l_Lean_Meta_mkEqRefl(x_135, x_3, x_4, x_5, x_6, x_78);
if (lean_obj_tag(x_136) == 0)
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_138 = lean_ctor_get(x_136, 0);
x_139 = lean_mk_string_unchecked("True", 4, 4);
x_140 = l_Lean_Name_mkStr1(x_139);
x_141 = l_Lean_Expr_const___override(x_140, x_134);
x_142 = lean_mk_string_unchecked("eq_true_of_decide", 17, 17);
x_143 = l_Lean_Name_mkStr1(x_142);
x_144 = l_Lean_Expr_const___override(x_143, x_134);
x_145 = l_Lean_Expr_appArg_x21(x_34);
lean_dec(x_34);
x_146 = lean_unsigned_to_nat(3u);
x_147 = lean_mk_empty_array_with_capacity(x_146);
x_148 = lean_array_push(x_147, x_1);
x_149 = lean_array_push(x_148, x_145);
x_150 = lean_array_push(x_149, x_138);
x_151 = l_Lean_mkAppN(x_144, x_150);
lean_dec(x_150);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_153 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_153, 0, x_141);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set_uint8(x_153, sizeof(void*)*2, x_29);
x_154 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_136, 0, x_154);
return x_136;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_155 = lean_ctor_get(x_136, 0);
x_156 = lean_ctor_get(x_136, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_136);
x_157 = lean_mk_string_unchecked("True", 4, 4);
x_158 = l_Lean_Name_mkStr1(x_157);
x_159 = l_Lean_Expr_const___override(x_158, x_134);
x_160 = lean_mk_string_unchecked("eq_true_of_decide", 17, 17);
x_161 = l_Lean_Name_mkStr1(x_160);
x_162 = l_Lean_Expr_const___override(x_161, x_134);
x_163 = l_Lean_Expr_appArg_x21(x_34);
lean_dec(x_34);
x_164 = lean_unsigned_to_nat(3u);
x_165 = lean_mk_empty_array_with_capacity(x_164);
x_166 = lean_array_push(x_165, x_1);
x_167 = lean_array_push(x_166, x_163);
x_168 = lean_array_push(x_167, x_155);
x_169 = l_Lean_mkAppN(x_162, x_168);
lean_dec(x_168);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_169);
x_171 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_171, 0, x_159);
lean_ctor_set(x_171, 1, x_170);
lean_ctor_set_uint8(x_171, sizeof(void*)*2, x_29);
x_172 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_172, 0, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_156);
return x_173;
}
}
else
{
uint8_t x_174; 
lean_dec(x_34);
lean_dec(x_1);
x_174 = !lean_is_exclusive(x_136);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_136, 0);
x_176 = lean_ctor_get(x_136, 1);
lean_inc(x_176);
lean_inc(x_175);
x_15 = x_136;
x_16 = x_175;
x_17 = x_176;
goto block_20;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_136, 0);
x_178 = lean_ctor_get(x_136, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_136);
lean_inc(x_178);
lean_inc(x_177);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_15 = x_179;
x_16 = x_177;
x_17 = x_178;
goto block_20;
}
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_180 = lean_ctor_get(x_75, 0);
x_181 = lean_ctor_get(x_75, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_75);
x_182 = lean_mk_string_unchecked("Bool", 4, 4);
x_183 = lean_mk_string_unchecked("true", 4, 4);
lean_inc(x_182);
x_184 = l_Lean_Name_mkStr2(x_182, x_183);
x_185 = l_Lean_Expr_isConstOf(x_180, x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; 
lean_dec(x_184);
x_186 = lean_mk_string_unchecked("false", 5, 5);
x_187 = l_Lean_Name_mkStr2(x_182, x_186);
x_188 = l_Lean_Expr_isConstOf(x_180, x_187);
lean_dec(x_180);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_187);
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_189 = lean_box(0);
x_190 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_190, 0, x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_181);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_box(0);
x_193 = l_Lean_Expr_const___override(x_187, x_192);
x_194 = l_Lean_Meta_mkEqRefl(x_193, x_3, x_4, x_5, x_6, x_181);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_197 = x_194;
} else {
 lean_dec_ref(x_194);
 x_197 = lean_box(0);
}
x_198 = lean_mk_string_unchecked("False", 5, 5);
x_199 = l_Lean_Name_mkStr1(x_198);
x_200 = l_Lean_Expr_const___override(x_199, x_192);
x_201 = lean_mk_string_unchecked("eq_false_of_decide", 18, 18);
x_202 = l_Lean_Name_mkStr1(x_201);
x_203 = l_Lean_Expr_const___override(x_202, x_192);
x_204 = l_Lean_Expr_appArg_x21(x_34);
lean_dec(x_34);
x_205 = lean_unsigned_to_nat(3u);
x_206 = lean_mk_empty_array_with_capacity(x_205);
x_207 = lean_array_push(x_206, x_1);
x_208 = lean_array_push(x_207, x_204);
x_209 = lean_array_push(x_208, x_195);
x_210 = l_Lean_mkAppN(x_203, x_209);
lean_dec(x_209);
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_210);
x_212 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_212, 0, x_200);
lean_ctor_set(x_212, 1, x_211);
lean_ctor_set_uint8(x_212, sizeof(void*)*2, x_29);
x_213 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_213, 0, x_212);
if (lean_is_scalar(x_197)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_197;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_196);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_34);
lean_dec(x_1);
x_215 = lean_ctor_get(x_194, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_194, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_217 = x_194;
} else {
 lean_dec_ref(x_194);
 x_217 = lean_box(0);
}
lean_inc(x_216);
lean_inc(x_215);
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_216);
x_15 = x_218;
x_16 = x_215;
x_17 = x_216;
goto block_20;
}
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_182);
lean_dec(x_180);
x_219 = lean_box(0);
x_220 = l_Lean_Expr_const___override(x_184, x_219);
x_221 = l_Lean_Meta_mkEqRefl(x_220, x_3, x_4, x_5, x_6, x_181);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
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
x_225 = lean_mk_string_unchecked("True", 4, 4);
x_226 = l_Lean_Name_mkStr1(x_225);
x_227 = l_Lean_Expr_const___override(x_226, x_219);
x_228 = lean_mk_string_unchecked("eq_true_of_decide", 17, 17);
x_229 = l_Lean_Name_mkStr1(x_228);
x_230 = l_Lean_Expr_const___override(x_229, x_219);
x_231 = l_Lean_Expr_appArg_x21(x_34);
lean_dec(x_34);
x_232 = lean_unsigned_to_nat(3u);
x_233 = lean_mk_empty_array_with_capacity(x_232);
x_234 = lean_array_push(x_233, x_1);
x_235 = lean_array_push(x_234, x_231);
x_236 = lean_array_push(x_235, x_222);
x_237 = l_Lean_mkAppN(x_230, x_236);
lean_dec(x_236);
x_238 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_238, 0, x_237);
x_239 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_239, 0, x_227);
lean_ctor_set(x_239, 1, x_238);
lean_ctor_set_uint8(x_239, sizeof(void*)*2, x_29);
x_240 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_240, 0, x_239);
if (lean_is_scalar(x_224)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_224;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_223);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_34);
lean_dec(x_1);
x_242 = lean_ctor_get(x_221, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_221, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_244 = x_221;
} else {
 lean_dec_ref(x_221);
 x_244 = lean_box(0);
}
lean_inc(x_243);
lean_inc(x_242);
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
x_15 = x_245;
x_16 = x_242;
x_17 = x_243;
goto block_20;
}
}
}
}
else
{
uint8_t x_246; 
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_246 = !lean_is_exclusive(x_75);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_75, 0);
x_248 = lean_ctor_get(x_75, 1);
lean_inc(x_248);
lean_inc(x_247);
x_15 = x_75;
x_16 = x_247;
x_17 = x_248;
goto block_20;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_75, 0);
x_250 = lean_ctor_get(x_75, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_75);
lean_inc(x_250);
lean_inc(x_249);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
x_15 = x_251;
x_16 = x_249;
x_17 = x_250;
goto block_20;
}
}
}
else
{
uint8_t x_252; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_252 = !lean_is_exclusive(x_33);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_33, 0);
x_254 = lean_ctor_get(x_33, 1);
lean_inc(x_254);
lean_inc(x_253);
x_15 = x_33;
x_16 = x_253;
x_17 = x_254;
goto block_20;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_33, 0);
x_256 = lean_ctor_get(x_33, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_33);
lean_inc(x_256);
lean_inc(x_255);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
x_15 = x_257;
x_16 = x_255;
x_17 = x_256;
goto block_20;
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
goto block_28;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
goto block_28;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
goto block_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpUsingDecide(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_31; uint8_t x_32; 
x_23 = l_Lean_Meta_Simp_getConfig___redArg(x_3, x_9);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_31 = lean_ctor_get_uint8(x_24, sizeof(void*)*2 + 9);
lean_dec(x_24);
if (x_31 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_261 = lean_box(0);
x_262 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_262, 0, x_261);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_25);
return x_263;
}
else
{
uint8_t x_264; 
x_264 = l_Lean_Expr_hasFVar(x_1);
if (x_264 == 0)
{
uint8_t x_265; 
x_265 = l_Lean_Expr_hasMVar(x_1);
x_32 = x_265;
goto block_260;
}
else
{
x_32 = x_264;
goto block_260;
}
}
block_16:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
lean_dec(x_10);
return x_11;
}
}
block_22:
{
uint8_t x_20; 
x_20 = l_Lean_Exception_isInterrupt(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Exception_isRuntime(x_18);
lean_dec(x_18);
x_10 = x_19;
x_11 = x_17;
x_12 = x_21;
goto block_16;
}
else
{
lean_dec(x_18);
x_10 = x_19;
x_11 = x_17;
x_12 = x_20;
goto block_16;
}
}
block_30:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
if (lean_is_scalar(x_26)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_26;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
block_260:
{
if (x_32 == 0)
{
uint8_t x_33; 
lean_inc(x_1);
x_33 = l_Lean_Expr_isTrue(x_1);
if (x_33 == 0)
{
uint8_t x_34; 
lean_inc(x_1);
x_34 = l_Lean_Expr_isFalse(x_1);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_26);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_35 = l_Lean_Meta_mkDecide(x_1, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; uint64_t x_59; lean_object* x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint8_t x_64; uint64_t x_65; uint64_t x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_box(1);
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
x_58 = lean_unbox(x_38);
lean_ctor_set_uint8(x_57, 9, x_58);
lean_ctor_set_uint8(x_57, 10, x_49);
lean_ctor_set_uint8(x_57, 11, x_50);
lean_ctor_set_uint8(x_57, 12, x_51);
lean_ctor_set_uint8(x_57, 13, x_52);
lean_ctor_set_uint8(x_57, 14, x_53);
lean_ctor_set_uint8(x_57, 15, x_54);
lean_ctor_set_uint8(x_57, 16, x_55);
lean_ctor_set_uint8(x_57, 17, x_56);
x_59 = lean_ctor_get_uint64(x_5, sizeof(void*)*7);
x_60 = lean_unsigned_to_nat(2u);
x_61 = lean_uint64_of_nat(x_60);
x_62 = lean_uint64_shift_right(x_59, x_61);
x_63 = lean_uint64_shift_left(x_62, x_61);
x_64 = lean_unbox(x_38);
x_65 = l_Lean_Meta_TransparencyMode_toUInt64(x_64);
x_66 = lean_uint64_lor(x_63, x_65);
x_67 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 8);
x_68 = lean_ctor_get(x_5, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_5, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_5, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_5, 4);
lean_inc(x_71);
x_72 = lean_ctor_get(x_5, 5);
lean_inc(x_72);
x_73 = lean_ctor_get(x_5, 6);
lean_inc(x_73);
x_74 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_75 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
x_76 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_76, 0, x_57);
lean_ctor_set(x_76, 1, x_68);
lean_ctor_set(x_76, 2, x_69);
lean_ctor_set(x_76, 3, x_70);
lean_ctor_set(x_76, 4, x_71);
lean_ctor_set(x_76, 5, x_72);
lean_ctor_set(x_76, 6, x_73);
lean_ctor_set_uint64(x_76, sizeof(void*)*7, x_66);
lean_ctor_set_uint8(x_76, sizeof(void*)*7 + 8, x_67);
lean_ctor_set_uint8(x_76, sizeof(void*)*7 + 9, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*7 + 10, x_75);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_36);
x_77 = lean_whnf(x_36, x_76, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
x_81 = lean_mk_string_unchecked("Bool", 4, 4);
x_82 = lean_mk_string_unchecked("true", 4, 4);
lean_inc(x_81);
x_83 = l_Lean_Name_mkStr2(x_81, x_82);
x_84 = l_Lean_Expr_isConstOf(x_79, x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_dec(x_83);
x_85 = lean_mk_string_unchecked("false", 5, 5);
x_86 = l_Lean_Name_mkStr2(x_81, x_85);
x_87 = l_Lean_Expr_isConstOf(x_79, x_86);
lean_dec(x_79);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_86);
lean_dec(x_36);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_77, 0, x_89);
return x_77;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_free_object(x_77);
x_90 = lean_box(0);
x_91 = l_Lean_Expr_const___override(x_86, x_90);
x_92 = l_Lean_Meta_mkEqRefl(x_91, x_5, x_6, x_7, x_8, x_80);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = lean_mk_string_unchecked("False", 5, 5);
x_96 = l_Lean_Name_mkStr1(x_95);
x_97 = l_Lean_Expr_const___override(x_96, x_90);
x_98 = lean_mk_string_unchecked("eq_false_of_decide", 18, 18);
x_99 = l_Lean_Name_mkStr1(x_98);
x_100 = l_Lean_Expr_const___override(x_99, x_90);
x_101 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_102 = lean_unsigned_to_nat(3u);
x_103 = lean_mk_empty_array_with_capacity(x_102);
x_104 = lean_array_push(x_103, x_1);
x_105 = lean_array_push(x_104, x_101);
x_106 = lean_array_push(x_105, x_94);
x_107 = l_Lean_mkAppN(x_100, x_106);
lean_dec(x_106);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_109, 0, x_97);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*2, x_31);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_92, 0, x_110);
return x_92;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_111 = lean_ctor_get(x_92, 0);
x_112 = lean_ctor_get(x_92, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_92);
x_113 = lean_mk_string_unchecked("False", 5, 5);
x_114 = l_Lean_Name_mkStr1(x_113);
x_115 = l_Lean_Expr_const___override(x_114, x_90);
x_116 = lean_mk_string_unchecked("eq_false_of_decide", 18, 18);
x_117 = l_Lean_Name_mkStr1(x_116);
x_118 = l_Lean_Expr_const___override(x_117, x_90);
x_119 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_120 = lean_unsigned_to_nat(3u);
x_121 = lean_mk_empty_array_with_capacity(x_120);
x_122 = lean_array_push(x_121, x_1);
x_123 = lean_array_push(x_122, x_119);
x_124 = lean_array_push(x_123, x_111);
x_125 = l_Lean_mkAppN(x_118, x_124);
lean_dec(x_124);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_127, 0, x_115);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set_uint8(x_127, sizeof(void*)*2, x_31);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_112);
return x_129;
}
}
else
{
uint8_t x_130; 
lean_dec(x_36);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_92);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_92, 0);
x_132 = lean_ctor_get(x_92, 1);
lean_inc(x_132);
lean_inc(x_131);
x_17 = x_92;
x_18 = x_131;
x_19 = x_132;
goto block_22;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_92, 0);
x_134 = lean_ctor_get(x_92, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_92);
lean_inc(x_134);
lean_inc(x_133);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_17 = x_135;
x_18 = x_133;
x_19 = x_134;
goto block_22;
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_81);
lean_free_object(x_77);
lean_dec(x_79);
x_136 = lean_box(0);
x_137 = l_Lean_Expr_const___override(x_83, x_136);
x_138 = l_Lean_Meta_mkEqRefl(x_137, x_5, x_6, x_7, x_8, x_80);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = lean_mk_string_unchecked("True", 4, 4);
x_142 = l_Lean_Name_mkStr1(x_141);
x_143 = l_Lean_Expr_const___override(x_142, x_136);
x_144 = lean_mk_string_unchecked("eq_true_of_decide", 17, 17);
x_145 = l_Lean_Name_mkStr1(x_144);
x_146 = l_Lean_Expr_const___override(x_145, x_136);
x_147 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_148 = lean_unsigned_to_nat(3u);
x_149 = lean_mk_empty_array_with_capacity(x_148);
x_150 = lean_array_push(x_149, x_1);
x_151 = lean_array_push(x_150, x_147);
x_152 = lean_array_push(x_151, x_140);
x_153 = l_Lean_mkAppN(x_146, x_152);
lean_dec(x_152);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_155, 0, x_143);
lean_ctor_set(x_155, 1, x_154);
lean_ctor_set_uint8(x_155, sizeof(void*)*2, x_31);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_138, 0, x_156);
return x_138;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_157 = lean_ctor_get(x_138, 0);
x_158 = lean_ctor_get(x_138, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_138);
x_159 = lean_mk_string_unchecked("True", 4, 4);
x_160 = l_Lean_Name_mkStr1(x_159);
x_161 = l_Lean_Expr_const___override(x_160, x_136);
x_162 = lean_mk_string_unchecked("eq_true_of_decide", 17, 17);
x_163 = l_Lean_Name_mkStr1(x_162);
x_164 = l_Lean_Expr_const___override(x_163, x_136);
x_165 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_166 = lean_unsigned_to_nat(3u);
x_167 = lean_mk_empty_array_with_capacity(x_166);
x_168 = lean_array_push(x_167, x_1);
x_169 = lean_array_push(x_168, x_165);
x_170 = lean_array_push(x_169, x_157);
x_171 = l_Lean_mkAppN(x_164, x_170);
lean_dec(x_170);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_171);
x_173 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_173, 0, x_161);
lean_ctor_set(x_173, 1, x_172);
lean_ctor_set_uint8(x_173, sizeof(void*)*2, x_31);
x_174 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_174, 0, x_173);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_158);
return x_175;
}
}
else
{
uint8_t x_176; 
lean_dec(x_36);
lean_dec(x_1);
x_176 = !lean_is_exclusive(x_138);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_138, 0);
x_178 = lean_ctor_get(x_138, 1);
lean_inc(x_178);
lean_inc(x_177);
x_17 = x_138;
x_18 = x_177;
x_19 = x_178;
goto block_22;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_138, 0);
x_180 = lean_ctor_get(x_138, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_138);
lean_inc(x_180);
lean_inc(x_179);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_17 = x_181;
x_18 = x_179;
x_19 = x_180;
goto block_22;
}
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_182 = lean_ctor_get(x_77, 0);
x_183 = lean_ctor_get(x_77, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_77);
x_184 = lean_mk_string_unchecked("Bool", 4, 4);
x_185 = lean_mk_string_unchecked("true", 4, 4);
lean_inc(x_184);
x_186 = l_Lean_Name_mkStr2(x_184, x_185);
x_187 = l_Lean_Expr_isConstOf(x_182, x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; 
lean_dec(x_186);
x_188 = lean_mk_string_unchecked("false", 5, 5);
x_189 = l_Lean_Name_mkStr2(x_184, x_188);
x_190 = l_Lean_Expr_isConstOf(x_182, x_189);
lean_dec(x_182);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_189);
lean_dec(x_36);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_191 = lean_box(0);
x_192 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_192, 0, x_191);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_183);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_box(0);
x_195 = l_Lean_Expr_const___override(x_189, x_194);
x_196 = l_Lean_Meta_mkEqRefl(x_195, x_5, x_6, x_7, x_8, x_183);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_199 = x_196;
} else {
 lean_dec_ref(x_196);
 x_199 = lean_box(0);
}
x_200 = lean_mk_string_unchecked("False", 5, 5);
x_201 = l_Lean_Name_mkStr1(x_200);
x_202 = l_Lean_Expr_const___override(x_201, x_194);
x_203 = lean_mk_string_unchecked("eq_false_of_decide", 18, 18);
x_204 = l_Lean_Name_mkStr1(x_203);
x_205 = l_Lean_Expr_const___override(x_204, x_194);
x_206 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_207 = lean_unsigned_to_nat(3u);
x_208 = lean_mk_empty_array_with_capacity(x_207);
x_209 = lean_array_push(x_208, x_1);
x_210 = lean_array_push(x_209, x_206);
x_211 = lean_array_push(x_210, x_197);
x_212 = l_Lean_mkAppN(x_205, x_211);
lean_dec(x_211);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_214 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_214, 0, x_202);
lean_ctor_set(x_214, 1, x_213);
lean_ctor_set_uint8(x_214, sizeof(void*)*2, x_31);
x_215 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_215, 0, x_214);
if (lean_is_scalar(x_199)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_199;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_198);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_36);
lean_dec(x_1);
x_217 = lean_ctor_get(x_196, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_196, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_219 = x_196;
} else {
 lean_dec_ref(x_196);
 x_219 = lean_box(0);
}
lean_inc(x_218);
lean_inc(x_217);
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_217);
lean_ctor_set(x_220, 1, x_218);
x_17 = x_220;
x_18 = x_217;
x_19 = x_218;
goto block_22;
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_184);
lean_dec(x_182);
x_221 = lean_box(0);
x_222 = l_Lean_Expr_const___override(x_186, x_221);
x_223 = l_Lean_Meta_mkEqRefl(x_222, x_5, x_6, x_7, x_8, x_183);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_226 = x_223;
} else {
 lean_dec_ref(x_223);
 x_226 = lean_box(0);
}
x_227 = lean_mk_string_unchecked("True", 4, 4);
x_228 = l_Lean_Name_mkStr1(x_227);
x_229 = l_Lean_Expr_const___override(x_228, x_221);
x_230 = lean_mk_string_unchecked("eq_true_of_decide", 17, 17);
x_231 = l_Lean_Name_mkStr1(x_230);
x_232 = l_Lean_Expr_const___override(x_231, x_221);
x_233 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_234 = lean_unsigned_to_nat(3u);
x_235 = lean_mk_empty_array_with_capacity(x_234);
x_236 = lean_array_push(x_235, x_1);
x_237 = lean_array_push(x_236, x_233);
x_238 = lean_array_push(x_237, x_224);
x_239 = l_Lean_mkAppN(x_232, x_238);
lean_dec(x_238);
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_239);
x_241 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_241, 0, x_229);
lean_ctor_set(x_241, 1, x_240);
lean_ctor_set_uint8(x_241, sizeof(void*)*2, x_31);
x_242 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_242, 0, x_241);
if (lean_is_scalar(x_226)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_226;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_225);
return x_243;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_36);
lean_dec(x_1);
x_244 = lean_ctor_get(x_223, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_223, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_246 = x_223;
} else {
 lean_dec_ref(x_223);
 x_246 = lean_box(0);
}
lean_inc(x_245);
lean_inc(x_244);
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_245);
x_17 = x_247;
x_18 = x_244;
x_19 = x_245;
goto block_22;
}
}
}
}
else
{
uint8_t x_248; 
lean_dec(x_36);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_248 = !lean_is_exclusive(x_77);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_77, 0);
x_250 = lean_ctor_get(x_77, 1);
lean_inc(x_250);
lean_inc(x_249);
x_17 = x_77;
x_18 = x_249;
x_19 = x_250;
goto block_22;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_77, 0);
x_252 = lean_ctor_get(x_77, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_77);
lean_inc(x_252);
lean_inc(x_251);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
x_17 = x_253;
x_18 = x_251;
x_19 = x_252;
goto block_22;
}
}
}
else
{
uint8_t x_254; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_254 = !lean_is_exclusive(x_35);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_35, 0);
x_256 = lean_ctor_get(x_35, 1);
lean_inc(x_256);
lean_inc(x_255);
x_17 = x_35;
x_18 = x_255;
x_19 = x_256;
goto block_22;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_35, 0);
x_258 = lean_ctor_get(x_35, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_35);
lean_inc(x_258);
lean_inc(x_257);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
x_17 = x_259;
x_18 = x_257;
x_19 = x_258;
goto block_22;
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
goto block_30;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
goto block_30;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
goto block_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpUsingDecide___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_simpUsingDecide___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpUsingDecide___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_simpUsingDecide(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_isNatExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_3);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_8, x_3, x_9);
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_Expr_cleanupAnnotations(x_12);
x_14 = lean_mk_string_unchecked("Nat", 3, 3);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = l_Lean_Expr_isConstOf(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
x_17 = lean_box(x_16);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = l_Lean_Expr_cleanupAnnotations(x_18);
x_21 = lean_mk_string_unchecked("Nat", 3, 3);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = l_Lean_Expr_isConstOf(x_20, x_22);
lean_dec(x_22);
lean_dec(x_20);
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_13; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Meta_Simp_getConfig___redArg(x_2, x_7);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*2 + 10);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_dec(x_18);
lean_inc(x_1);
x_30 = l_Lean_Meta_Simp_Arith_isLinearCnstr(x_1);
if (x_30 == 0)
{
lean_object* x_31; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_31 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_isNatExpr(x_1, x_3, x_4, x_5, x_6, x_29);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_unbox(x_33);
x_36 = l_Lean_Meta_Simp_Arith_isLinearTerm(x_1, x_35);
if (x_36 == 0)
{
uint8_t x_37; 
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_2);
x_37 = l_Lean_Meta_Simp_Arith_isDvdCnstr(x_1);
if (x_37 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = x_34;
goto block_12;
}
else
{
lean_object* x_38; 
x_38 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(x_1, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_8 = x_40;
goto block_12;
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_38, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
lean_ctor_set(x_39, 0, x_46);
x_47 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_39);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_20);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_38, 0, x_48);
return x_38;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_39, 0);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_dec(x_38);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
lean_ctor_set(x_39, 0, x_52);
x_53 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_39);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_20);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_56 = lean_ctor_get(x_39, 0);
lean_inc(x_56);
lean_dec(x_39);
x_57 = lean_ctor_get(x_38, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_58 = x_38;
} else {
 lean_dec_ref(x_38);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*2, x_20);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
if (lean_is_scalar(x_58)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_58;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_57);
return x_64;
}
}
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_38);
if (x_65 == 0)
{
return x_38;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_38, 0);
x_67 = lean_ctor_get(x_38, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_38);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_69; uint8_t x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_2, 7);
lean_inc(x_69);
lean_dec(x_2);
x_70 = lean_unbox(x_33);
x_71 = l_Lean_Meta_Simp_Arith_parentIsTarget(x_69, x_70);
if (x_71 == 0)
{
uint8_t x_72; 
lean_free_object(x_31);
x_72 = lean_unbox(x_33);
lean_dec(x_33);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(x_1, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_13 = x_75;
goto block_17;
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_74);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_73);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_74, 0);
x_79 = lean_ctor_get(x_73, 0);
lean_dec(x_79);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
lean_ctor_set(x_74, 0, x_81);
x_82 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set_uint8(x_82, sizeof(void*)*2, x_20);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_73, 0, x_83);
return x_73;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_84 = lean_ctor_get(x_74, 0);
x_85 = lean_ctor_get(x_73, 1);
lean_inc(x_85);
lean_dec(x_73);
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
lean_ctor_set(x_74, 0, x_87);
x_88 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_74);
lean_ctor_set_uint8(x_88, sizeof(void*)*2, x_20);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_85);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_91 = lean_ctor_get(x_74, 0);
lean_inc(x_91);
lean_dec(x_74);
x_92 = lean_ctor_get(x_73, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_93 = x_73;
} else {
 lean_dec_ref(x_73);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
lean_dec(x_91);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*2, x_20);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
if (lean_is_scalar(x_93)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_93;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_92);
return x_99;
}
}
}
else
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_73);
if (x_100 == 0)
{
return x_73;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_73, 0);
x_102 = lean_ctor_get(x_73, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_73);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; 
x_104 = l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(x_1, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_13 = x_106;
goto block_17;
}
else
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_105);
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_104);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_105, 0);
x_110 = lean_ctor_get(x_104, 0);
lean_dec(x_110);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec(x_109);
lean_ctor_set(x_105, 0, x_112);
x_113 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_105);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_20);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_104, 0, x_114);
return x_104;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_105, 0);
x_116 = lean_ctor_get(x_104, 1);
lean_inc(x_116);
lean_dec(x_104);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
lean_ctor_set(x_105, 0, x_118);
x_119 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_105);
lean_ctor_set_uint8(x_119, sizeof(void*)*2, x_20);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_116);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_122 = lean_ctor_get(x_105, 0);
lean_inc(x_122);
lean_dec(x_105);
x_123 = lean_ctor_get(x_104, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_124 = x_104;
} else {
 lean_dec_ref(x_104);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_122, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_122, 1);
lean_inc(x_126);
lean_dec(x_122);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set_uint8(x_128, sizeof(void*)*2, x_20);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
if (lean_is_scalar(x_124)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_124;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_123);
return x_130;
}
}
}
else
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_104);
if (x_131 == 0)
{
return x_104;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_104, 0);
x_133 = lean_ctor_get(x_104, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_104);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_136, 0, x_1);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set_uint8(x_136, sizeof(void*)*2, x_30);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_138 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_31, 0, x_138);
return x_31;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_142; 
x_139 = lean_ctor_get(x_31, 0);
x_140 = lean_ctor_get(x_31, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_31);
x_141 = lean_unbox(x_139);
x_142 = l_Lean_Meta_Simp_Arith_isLinearTerm(x_1, x_141);
if (x_142 == 0)
{
uint8_t x_143; 
lean_dec(x_139);
lean_dec(x_2);
x_143 = l_Lean_Meta_Simp_Arith_isDvdCnstr(x_1);
if (x_143 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = x_140;
goto block_12;
}
else
{
lean_object* x_144; 
x_144 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(x_1, x_3, x_4, x_5, x_6, x_140);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_8 = x_146;
goto block_12;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_144, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_150 = x_144;
} else {
 lean_dec_ref(x_144);
 x_150 = lean_box(0);
}
x_151 = lean_ctor_get(x_147, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_147, 1);
lean_inc(x_152);
lean_dec(x_147);
if (lean_is_scalar(x_148)) {
 x_153 = lean_alloc_ctor(1, 1, 0);
} else {
 x_153 = x_148;
}
lean_ctor_set(x_153, 0, x_152);
x_154 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set_uint8(x_154, sizeof(void*)*2, x_20);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
if (lean_is_scalar(x_150)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_150;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_149);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_144, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_144, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_159 = x_144;
} else {
 lean_dec_ref(x_144);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
else
{
lean_object* x_161; uint8_t x_162; uint8_t x_163; 
x_161 = lean_ctor_get(x_2, 7);
lean_inc(x_161);
lean_dec(x_2);
x_162 = lean_unbox(x_139);
x_163 = l_Lean_Meta_Simp_Arith_parentIsTarget(x_161, x_162);
if (x_163 == 0)
{
uint8_t x_164; 
x_164 = lean_unbox(x_139);
lean_dec(x_139);
if (x_164 == 0)
{
lean_object* x_165; 
x_165 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(x_1, x_3, x_4, x_5, x_6, x_140);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_13 = x_167;
goto block_17;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 x_169 = x_166;
} else {
 lean_dec_ref(x_166);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_165, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_171 = x_165;
} else {
 lean_dec_ref(x_165);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_168, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_168, 1);
lean_inc(x_173);
lean_dec(x_168);
if (lean_is_scalar(x_169)) {
 x_174 = lean_alloc_ctor(1, 1, 0);
} else {
 x_174 = x_169;
}
lean_ctor_set(x_174, 0, x_173);
x_175 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_174);
lean_ctor_set_uint8(x_175, sizeof(void*)*2, x_20);
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_175);
if (lean_is_scalar(x_171)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_171;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_170);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = lean_ctor_get(x_165, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_165, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_180 = x_165;
} else {
 lean_dec_ref(x_165);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
else
{
lean_object* x_182; 
x_182 = l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(x_1, x_3, x_4, x_5, x_6, x_140);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; 
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_13 = x_184;
goto block_17;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_185 = lean_ctor_get(x_183, 0);
lean_inc(x_185);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 x_186 = x_183;
} else {
 lean_dec_ref(x_183);
 x_186 = lean_box(0);
}
x_187 = lean_ctor_get(x_182, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_188 = x_182;
} else {
 lean_dec_ref(x_182);
 x_188 = lean_box(0);
}
x_189 = lean_ctor_get(x_185, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_185, 1);
lean_inc(x_190);
lean_dec(x_185);
if (lean_is_scalar(x_186)) {
 x_191 = lean_alloc_ctor(1, 1, 0);
} else {
 x_191 = x_186;
}
lean_ctor_set(x_191, 0, x_190);
x_192 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_191);
lean_ctor_set_uint8(x_192, sizeof(void*)*2, x_20);
x_193 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_193, 0, x_192);
if (lean_is_scalar(x_188)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_188;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_187);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_195 = lean_ctor_get(x_182, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_182, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_197 = x_182;
} else {
 lean_dec_ref(x_182);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_139);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_199 = lean_box(0);
x_200 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_200, 0, x_1);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set_uint8(x_200, sizeof(void*)*2, x_30);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
x_202 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_202, 0, x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_140);
return x_203;
}
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
x_204 = !lean_is_exclusive(x_31);
if (x_204 == 0)
{
return x_31;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_31, 0);
x_206 = lean_ctor_get(x_31, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_31);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
else
{
lean_object* x_208; 
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_208 = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f(x_1, x_3, x_4, x_5, x_6, x_29);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_211 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(x_1, x_3, x_4, x_5, x_6, x_210);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(x_1, x_3, x_4, x_5, x_6, x_213);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
if (lean_obj_tag(x_215) == 0)
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_214);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_214, 0);
lean_dec(x_217);
x_218 = lean_box(0);
x_219 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_214, 0, x_219);
return x_214;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_220 = lean_ctor_get(x_214, 1);
lean_inc(x_220);
lean_dec(x_214);
x_221 = lean_box(0);
x_222 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_222, 0, x_221);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_220);
return x_223;
}
}
else
{
uint8_t x_224; 
x_224 = !lean_is_exclusive(x_215);
if (x_224 == 0)
{
uint8_t x_225; 
x_225 = !lean_is_exclusive(x_214);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_226 = lean_ctor_get(x_215, 0);
x_227 = lean_ctor_get(x_214, 0);
lean_dec(x_227);
x_228 = lean_ctor_get(x_226, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_226, 1);
lean_inc(x_229);
lean_dec(x_226);
lean_ctor_set(x_215, 0, x_229);
x_230 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_215);
lean_ctor_set_uint8(x_230, sizeof(void*)*2, x_20);
x_231 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_214, 0, x_231);
return x_214;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_232 = lean_ctor_get(x_215, 0);
x_233 = lean_ctor_get(x_214, 1);
lean_inc(x_233);
lean_dec(x_214);
x_234 = lean_ctor_get(x_232, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_232, 1);
lean_inc(x_235);
lean_dec(x_232);
lean_ctor_set(x_215, 0, x_235);
x_236 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_215);
lean_ctor_set_uint8(x_236, sizeof(void*)*2, x_20);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_236);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_233);
return x_238;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_239 = lean_ctor_get(x_215, 0);
lean_inc(x_239);
lean_dec(x_215);
x_240 = lean_ctor_get(x_214, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_241 = x_214;
} else {
 lean_dec_ref(x_214);
 x_241 = lean_box(0);
}
x_242 = lean_ctor_get(x_239, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_239, 1);
lean_inc(x_243);
lean_dec(x_239);
x_244 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_244, 0, x_243);
x_245 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_244);
lean_ctor_set_uint8(x_245, sizeof(void*)*2, x_20);
x_246 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_246, 0, x_245);
if (lean_is_scalar(x_241)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_241;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_240);
return x_247;
}
}
}
else
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_214);
if (x_248 == 0)
{
return x_214;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_214, 0);
x_250 = lean_ctor_get(x_214, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_214);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
}
else
{
uint8_t x_252; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_252 = !lean_is_exclusive(x_212);
if (x_252 == 0)
{
uint8_t x_253; 
x_253 = !lean_is_exclusive(x_211);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_254 = lean_ctor_get(x_212, 0);
x_255 = lean_ctor_get(x_211, 0);
lean_dec(x_255);
x_256 = lean_ctor_get(x_254, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_254, 1);
lean_inc(x_257);
lean_dec(x_254);
lean_ctor_set(x_212, 0, x_257);
x_258 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_212);
lean_ctor_set_uint8(x_258, sizeof(void*)*2, x_20);
x_259 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_211, 0, x_259);
return x_211;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_260 = lean_ctor_get(x_212, 0);
x_261 = lean_ctor_get(x_211, 1);
lean_inc(x_261);
lean_dec(x_211);
x_262 = lean_ctor_get(x_260, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_260, 1);
lean_inc(x_263);
lean_dec(x_260);
lean_ctor_set(x_212, 0, x_263);
x_264 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_212);
lean_ctor_set_uint8(x_264, sizeof(void*)*2, x_20);
x_265 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_265, 0, x_264);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_261);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_267 = lean_ctor_get(x_212, 0);
lean_inc(x_267);
lean_dec(x_212);
x_268 = lean_ctor_get(x_211, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_269 = x_211;
} else {
 lean_dec_ref(x_211);
 x_269 = lean_box(0);
}
x_270 = lean_ctor_get(x_267, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_267, 1);
lean_inc(x_271);
lean_dec(x_267);
x_272 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_272, 0, x_271);
x_273 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_273, 0, x_270);
lean_ctor_set(x_273, 1, x_272);
lean_ctor_set_uint8(x_273, sizeof(void*)*2, x_20);
x_274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_274, 0, x_273);
if (lean_is_scalar(x_269)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_269;
}
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_268);
return x_275;
}
}
}
else
{
uint8_t x_276; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_276 = !lean_is_exclusive(x_211);
if (x_276 == 0)
{
return x_211;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_211, 0);
x_278 = lean_ctor_get(x_211, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_211);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
}
else
{
uint8_t x_280; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_280 = !lean_is_exclusive(x_209);
if (x_280 == 0)
{
uint8_t x_281; 
x_281 = !lean_is_exclusive(x_208);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_282 = lean_ctor_get(x_209, 0);
x_283 = lean_ctor_get(x_208, 0);
lean_dec(x_283);
x_284 = lean_ctor_get(x_282, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_282, 1);
lean_inc(x_285);
lean_dec(x_282);
lean_ctor_set(x_209, 0, x_285);
x_286 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_209);
lean_ctor_set_uint8(x_286, sizeof(void*)*2, x_20);
x_287 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_208, 0, x_287);
return x_208;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_288 = lean_ctor_get(x_209, 0);
x_289 = lean_ctor_get(x_208, 1);
lean_inc(x_289);
lean_dec(x_208);
x_290 = lean_ctor_get(x_288, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_288, 1);
lean_inc(x_291);
lean_dec(x_288);
lean_ctor_set(x_209, 0, x_291);
x_292 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_209);
lean_ctor_set_uint8(x_292, sizeof(void*)*2, x_20);
x_293 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_293, 0, x_292);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_289);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_295 = lean_ctor_get(x_209, 0);
lean_inc(x_295);
lean_dec(x_209);
x_296 = lean_ctor_get(x_208, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_297 = x_208;
} else {
 lean_dec_ref(x_208);
 x_297 = lean_box(0);
}
x_298 = lean_ctor_get(x_295, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_295, 1);
lean_inc(x_299);
lean_dec(x_295);
x_300 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_300, 0, x_299);
x_301 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_300);
lean_ctor_set_uint8(x_301, sizeof(void*)*2, x_20);
x_302 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_302, 0, x_301);
if (lean_is_scalar(x_297)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_297;
}
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_296);
return x_303;
}
}
}
else
{
uint8_t x_304; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_304 = !lean_is_exclusive(x_208);
if (x_304 == 0)
{
return x_208;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_208, 0);
x_306 = lean_ctor_get(x_208, 1);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_208);
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
return x_307;
}
}
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_simpArith___redArg(x_1, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_simpArith(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_57 = l_Lean_Expr_getAppNumArgs(x_1);
x_58 = lean_ctor_get(x_2, 0);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_58, x_59);
x_61 = lean_box(0);
x_62 = l_Lean_Expr_sort___override(x_61);
x_63 = lean_ctor_get(x_4, 1);
x_64 = lean_nat_dec_lt(x_6, x_63);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_5);
lean_ctor_set(x_65, 1, x_14);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_110; uint8_t x_111; 
x_66 = lean_nat_sub(x_57, x_60);
lean_dec(x_60);
lean_dec(x_57);
lean_inc(x_66);
x_67 = lean_mk_array(x_66, x_62);
x_68 = l_Lean_instInhabitedExpr;
lean_inc(x_1);
x_69 = l_Lean_Expr_getAppArgsN_loop(x_66, x_1, x_67);
x_70 = lean_ctor_get(x_5, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_71);
lean_dec(x_5);
x_72 = lean_array_get(x_68, x_69, x_6);
lean_dec(x_69);
x_110 = lean_array_get_size(x_3);
x_111 = lean_nat_dec_lt(x_6, x_110);
lean_dec(x_110);
if (x_111 == 0)
{
goto block_109;
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = l_Lean_Meta_instInhabitedParamInfo;
x_113 = lean_array_get(x_112, x_3, x_6);
x_114 = lean_ctor_get_uint8(x_113, sizeof(void*)*1 + 1);
lean_dec(x_113);
if (x_114 == 0)
{
if (x_111 == 0)
{
goto block_109;
}
else
{
lean_object* x_115; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_72);
x_115 = lean_simp(x_72, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_134; uint8_t x_135; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_134 = lean_ctor_get(x_116, 0);
lean_inc(x_134);
x_135 = lean_expr_eqv(x_134, x_72);
lean_dec(x_72);
lean_dec(x_134);
if (x_135 == 0)
{
lean_dec(x_70);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_118 = x_111;
x_119 = x_71;
x_120 = x_10;
x_121 = x_11;
x_122 = x_12;
x_123 = x_13;
goto block_133;
}
else
{
uint8_t x_136; 
x_136 = lean_unbox(x_70);
lean_dec(x_70);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_118 = x_136;
x_119 = x_71;
x_120 = x_10;
x_121 = x_11;
x_122 = x_12;
x_123 = x_13;
goto block_133;
}
block_133:
{
lean_object* x_124; 
x_124 = l_Lean_Meta_Simp_mkCongr(x_119, x_116, x_120, x_121, x_122, x_123, x_117);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_box(x_118);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_125);
x_15 = x_128;
x_16 = x_126;
goto block_20;
}
else
{
uint8_t x_129; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_124);
if (x_129 == 0)
{
return x_124;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_124, 0);
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_124);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_115);
if (x_137 == 0)
{
return x_115;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_115, 0);
x_139 = lean_ctor_get(x_115, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_115);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
}
else
{
goto block_109;
}
}
block_109:
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_74 = lean_infer_type(x_73, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_77 = l_Lean_Meta_whnfD(x_75, x_10, x_11, x_12, x_13, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Expr_isArrow(x_78);
lean_dec(x_78);
if (x_80 == 0)
{
lean_object* x_81; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_72);
x_81 = lean_dsimp(x_72, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_expr_eqv(x_82, x_72);
lean_dec(x_72);
if (x_84 == 0)
{
lean_dec(x_70);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_21 = x_82;
x_22 = x_64;
x_23 = x_71;
x_24 = x_10;
x_25 = x_11;
x_26 = x_12;
x_27 = x_13;
x_28 = x_83;
goto block_38;
}
else
{
if (x_80 == 0)
{
uint8_t x_85; 
x_85 = lean_unbox(x_70);
lean_dec(x_70);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_21 = x_82;
x_22 = x_85;
x_23 = x_71;
x_24 = x_10;
x_25 = x_11;
x_26 = x_12;
x_27 = x_13;
x_28 = x_83;
goto block_38;
}
else
{
lean_dec(x_70);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_21 = x_82;
x_22 = x_80;
x_23 = x_71;
x_24 = x_10;
x_25 = x_11;
x_26 = x_12;
x_27 = x_13;
x_28 = x_83;
goto block_38;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_81);
if (x_86 == 0)
{
return x_81;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_81, 0);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_81);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_72);
x_90 = lean_simp(x_72, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_79);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_expr_eqv(x_93, x_72);
lean_dec(x_72);
lean_dec(x_93);
if (x_94 == 0)
{
if (x_80 == 0)
{
uint8_t x_95; 
x_95 = lean_unbox(x_70);
lean_dec(x_70);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_39 = x_91;
x_40 = x_95;
x_41 = x_71;
x_42 = x_10;
x_43 = x_11;
x_44 = x_12;
x_45 = x_13;
x_46 = x_92;
goto block_56;
}
else
{
lean_dec(x_70);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_39 = x_91;
x_40 = x_80;
x_41 = x_71;
x_42 = x_10;
x_43 = x_11;
x_44 = x_12;
x_45 = x_13;
x_46 = x_92;
goto block_56;
}
}
else
{
uint8_t x_96; 
x_96 = lean_unbox(x_70);
lean_dec(x_70);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_39 = x_91;
x_40 = x_96;
x_41 = x_71;
x_42 = x_10;
x_43 = x_11;
x_44 = x_12;
x_45 = x_13;
x_46 = x_92;
goto block_56;
}
}
else
{
uint8_t x_97; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_90);
if (x_97 == 0)
{
return x_90;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_90, 0);
x_99 = lean_ctor_get(x_90, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_90);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_77);
if (x_101 == 0)
{
return x_77;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_77, 0);
x_103 = lean_ctor_get(x_77, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_77);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_74);
if (x_105 == 0)
{
return x_74;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_74, 0);
x_107 = lean_ctor_get(x_74, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_74);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
block_20:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_4, 2);
x_18 = lean_nat_add(x_6, x_17);
lean_dec(x_6);
x_5 = x_15;
x_6 = x_18;
x_14 = x_16;
goto _start;
}
block_38:
{
lean_object* x_29; 
x_29 = l_Lean_Meta_Simp_mkCongrFun(x_23, x_21, x_24, x_25, x_26, x_27, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_box(x_22);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
x_15 = x_33;
x_16 = x_31;
goto block_20;
}
else
{
uint8_t x_34; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
block_56:
{
lean_object* x_47; 
x_47 = l_Lean_Meta_Simp_mkCongr(x_41, x_39, x_42, x_43, x_44, x_45, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_box(x_40);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
x_15 = x_51;
x_16 = x_49;
goto block_20;
}
else
{
uint8_t x_52; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
return x_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_47, 0);
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_47);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = l_Lean_Expr_getAppNumArgs(x_1);
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_12, x_13);
x_15 = lean_box(0);
x_16 = l_Lean_Expr_sort___override(x_15);
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_nat_dec_lt(x_5, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_nat_sub(x_11, x_14);
lean_dec(x_14);
lean_dec(x_11);
lean_inc(x_20);
x_21 = lean_mk_array(x_20, x_16);
lean_inc(x_1);
x_22 = l_Lean_Expr_getAppArgsN_loop(x_20, x_1, x_21);
x_23 = lean_array_fget(x_22, x_5);
lean_dec(x_22);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l_Lean_Meta_Simp_mkCongrFun(x_4, x_23, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_3, 2);
x_28 = lean_nat_add(x_5, x_27);
lean_dec(x_5);
x_4 = x_25;
x_5 = x_28;
x_10 = x_26;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchDiscrs_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Expr_getAppNumArgs(x_2);
x_12 = l_Lean_Meta_Match_MatcherInfo_arity(x_1);
x_13 = lean_nat_dec_lt(x_11, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_14, x_15);
lean_dec(x_14);
x_17 = lean_nat_sub(x_11, x_16);
lean_dec(x_16);
lean_dec(x_11);
lean_inc(x_17);
x_18 = l_Lean_Expr_stripArgsN(x_2, x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_17);
lean_inc(x_18);
x_19 = l_Lean_Meta_getFunInfoNArgs(x_18, x_17, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = l_Lean_Expr_sort___override(x_23);
x_25 = lean_box(0);
x_26 = lean_box(1);
x_27 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_unbox(x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_28);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_inc(x_30);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_15);
x_32 = lean_box(x_13);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_34 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__0___redArg(x_2, x_1, x_22, x_31, x_33, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_31);
lean_dec(x_22);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
uint8_t x_38; 
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_34, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_34, 0, x_40);
return x_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_dec(x_34);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_dec(x_34);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_dec(x_35);
lean_inc(x_17);
x_46 = lean_mk_array(x_17, x_24);
lean_inc(x_2);
x_47 = l_Lean_Expr_getAppArgsN_loop(x_17, x_2, x_46);
x_48 = lean_array_get_size(x_47);
lean_dec(x_47);
lean_inc(x_30);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_30);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_15);
x_50 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__1___redArg(x_2, x_1, x_49, x_45, x_30, x_6, x_7, x_8, x_9, x_44);
lean_dec(x_49);
lean_dec(x_1);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_50, 0, x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_50);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_54);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_50);
if (x_58 == 0)
{
return x_50;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_50, 0);
x_60 = lean_ctor_get(x_50, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_50);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_34);
if (x_62 == 0)
{
return x_34;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_34, 0);
x_64 = lean_ctor_get(x_34, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_34);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_19);
if (x_66 == 0)
{
return x_19;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_19, 0);
x_68 = lean_ctor_get(x_19, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_19);
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
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_10);
return x_71;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_simpMatchDiscrs_x3f_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simpMatchCore_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_usize_dec_lt(x_4, x_3);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_17 = lean_array_uget(x_2, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_17);
x_18 = l_Lean_Meta_isRflTheorem(x_17, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; lean_object* x_71; uint8_t x_72; uint64_t x_73; lean_object* x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint8_t x_78; uint64_t x_79; uint64_t x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_22);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_mk_empty_array_with_capacity(x_41);
x_43 = lean_box(0);
lean_inc(x_17);
x_44 = l_Lean_Expr_const___override(x_17, x_43);
x_45 = lean_unsigned_to_nat(1000u);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_47, 0, x_17);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_15);
x_48 = lean_unbox(x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*1 + 1, x_48);
lean_inc(x_42);
x_49 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_42);
lean_ctor_set(x_49, 2, x_44);
lean_ctor_set(x_49, 3, x_45);
lean_ctor_set(x_49, 4, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*5, x_15);
x_50 = lean_unbox(x_46);
lean_ctor_set_uint8(x_49, sizeof(void*)*5 + 1, x_50);
x_51 = lean_unbox(x_19);
lean_dec(x_19);
lean_ctor_set_uint8(x_49, sizeof(void*)*5 + 2, x_51);
x_52 = lean_box(2);
x_53 = lean_ctor_get(x_9, 0);
x_54 = lean_ctor_get_uint8(x_53, 0);
x_55 = lean_ctor_get_uint8(x_53, 1);
x_56 = lean_ctor_get_uint8(x_53, 2);
x_57 = lean_ctor_get_uint8(x_53, 3);
x_58 = lean_ctor_get_uint8(x_53, 4);
x_59 = lean_ctor_get_uint8(x_53, 5);
x_60 = lean_ctor_get_uint8(x_53, 6);
x_61 = lean_ctor_get_uint8(x_53, 7);
x_62 = lean_ctor_get_uint8(x_53, 8);
x_63 = lean_ctor_get_uint8(x_53, 10);
x_64 = lean_ctor_get_uint8(x_53, 11);
x_65 = lean_ctor_get_uint8(x_53, 12);
x_66 = lean_ctor_get_uint8(x_53, 13);
x_67 = lean_ctor_get_uint8(x_53, 14);
x_68 = lean_ctor_get_uint8(x_53, 15);
x_69 = lean_ctor_get_uint8(x_53, 16);
x_70 = lean_ctor_get_uint8(x_53, 17);
x_71 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_71, 0, x_54);
lean_ctor_set_uint8(x_71, 1, x_55);
lean_ctor_set_uint8(x_71, 2, x_56);
lean_ctor_set_uint8(x_71, 3, x_57);
lean_ctor_set_uint8(x_71, 4, x_58);
lean_ctor_set_uint8(x_71, 5, x_59);
lean_ctor_set_uint8(x_71, 6, x_60);
lean_ctor_set_uint8(x_71, 7, x_61);
lean_ctor_set_uint8(x_71, 8, x_62);
x_72 = lean_unbox(x_52);
lean_ctor_set_uint8(x_71, 9, x_72);
lean_ctor_set_uint8(x_71, 10, x_63);
lean_ctor_set_uint8(x_71, 11, x_64);
lean_ctor_set_uint8(x_71, 12, x_65);
lean_ctor_set_uint8(x_71, 13, x_66);
lean_ctor_set_uint8(x_71, 14, x_67);
lean_ctor_set_uint8(x_71, 15, x_68);
lean_ctor_set_uint8(x_71, 16, x_69);
lean_ctor_set_uint8(x_71, 17, x_70);
x_73 = lean_ctor_get_uint64(x_9, sizeof(void*)*7);
x_74 = lean_unsigned_to_nat(2u);
x_75 = lean_uint64_of_nat(x_74);
x_76 = lean_uint64_shift_right(x_73, x_75);
x_77 = lean_uint64_shift_left(x_76, x_75);
x_78 = lean_unbox(x_52);
x_79 = l_Lean_Meta_TransparencyMode_toUInt64(x_78);
x_80 = lean_uint64_lor(x_77, x_79);
x_81 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 8);
x_82 = lean_ctor_get(x_9, 1);
x_83 = lean_ctor_get(x_9, 2);
x_84 = lean_ctor_get(x_9, 3);
x_85 = lean_ctor_get(x_9, 4);
x_86 = lean_ctor_get(x_9, 5);
x_87 = lean_ctor_get(x_9, 6);
x_88 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 9);
x_89 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 10);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
x_90 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_90, 0, x_71);
lean_ctor_set(x_90, 1, x_82);
lean_ctor_set(x_90, 2, x_83);
lean_ctor_set(x_90, 3, x_84);
lean_ctor_set(x_90, 4, x_85);
lean_ctor_set(x_90, 5, x_86);
lean_ctor_set(x_90, 6, x_87);
lean_ctor_set_uint64(x_90, sizeof(void*)*7, x_80);
lean_ctor_set_uint8(x_90, sizeof(void*)*7 + 8, x_81);
lean_ctor_set_uint8(x_90, sizeof(void*)*7 + 9, x_88);
lean_ctor_set_uint8(x_90, sizeof(void*)*7 + 10, x_89);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_91 = l_Lean_Meta_Simp_tryTheorem_x3f(x_1, x_49, x_6, x_7, x_8, x_90, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_24 = x_92;
x_25 = x_93;
goto block_40;
}
else
{
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
lean_dec(x_91);
x_24 = x_94;
x_25 = x_95;
goto block_40;
}
else
{
uint8_t x_96; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_91);
if (x_96 == 0)
{
return x_91;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_91, 0);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_91);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
block_40:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_26; size_t x_27; size_t x_28; 
lean_dec(x_21);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_usize_of_nat(x_26);
x_28 = lean_usize_add(x_4, x_27);
x_4 = x_28;
x_5 = x_23;
x_13 = x_25;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_24, 0, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_22);
if (lean_is_scalar(x_21)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_21;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_24, 0);
lean_inc(x_35);
lean_dec(x_24);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_22);
if (lean_is_scalar(x_21)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_21;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_25);
return x_39;
}
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_18);
if (x_100 == 0)
{
return x_18;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_18, 0);
x_102 = lean_ctor_get(x_18, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_18);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = lean_get_match_equations_for(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; size_t x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_size(x_14);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_usize_of_nat(x_19);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simpMatchCore_spec__0(x_2, x_14, x_18, x_20, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_6);
lean_dec(x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_21, 0, x_27);
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_21, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_23, 0);
lean_inc(x_34);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_34);
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_dec(x_21);
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
lean_dec(x_23);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_21);
if (x_38 == 0)
{
return x_21;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_21, 0);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_21);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_11);
if (x_42 == 0)
{
return x_11;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_11, 0);
x_44 = lean_ctor_get(x_11, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_11);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simpMatchCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simpMatchCore_spec__0(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_Simp_simpMatch_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_7, x_1);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_Simp_simpMatch_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_Simp_simpMatch_spec__0___redArg(x_1, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_Simp_getConfig___redArg(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*2 + 7);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_115; lean_object* x_116; uint64_t x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; 
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_22 = x_10;
} else {
 lean_dec_ref(x_10);
 x_22 = lean_box(0);
}
x_115 = lean_ctor_get(x_3, 3);
lean_inc(x_115);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get_uint64(x_115, sizeof(void*)*1);
lean_dec(x_115);
x_118 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 8);
x_119 = lean_ctor_get(x_5, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_5, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_5, 3);
lean_inc(x_121);
x_122 = lean_ctor_get(x_5, 4);
lean_inc(x_122);
x_123 = lean_ctor_get(x_5, 5);
lean_inc(x_123);
x_124 = lean_ctor_get(x_5, 6);
lean_inc(x_124);
x_125 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_126 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
x_127 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_127, 0, x_116);
lean_ctor_set(x_127, 1, x_119);
lean_ctor_set(x_127, 2, x_120);
lean_ctor_set(x_127, 3, x_121);
lean_ctor_set(x_127, 4, x_122);
lean_ctor_set(x_127, 5, x_123);
lean_ctor_set(x_127, 6, x_124);
lean_ctor_set_uint64(x_127, sizeof(void*)*7, x_117);
lean_ctor_set_uint8(x_127, sizeof(void*)*7 + 8, x_118);
lean_ctor_set_uint8(x_127, sizeof(void*)*7 + 9, x_125);
lean_ctor_set_uint8(x_127, sizeof(void*)*7 + 10, x_126);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_128 = l_Lean_Meta_reduceRecMatcher_x3f(x_1, x_127, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_23 = x_129;
x_24 = x_130;
goto block_114;
}
else
{
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_128, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
lean_dec(x_128);
x_23 = x_131;
x_24 = x_132;
goto block_114;
}
else
{
uint8_t x_133; 
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_128);
if (x_133 == 0)
{
return x_128;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_128, 0);
x_135 = lean_ctor_get(x_128, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_128);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
block_114:
{
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_25; 
lean_dec(x_22);
x_25 = l_Lean_Expr_getAppFn(x_1);
switch (lean_obj_tag(x_25)) {
case 0:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Expr_bvar___override(x_26);
x_28 = l_Lean_Meta_Simp_simpMatch___lam__0(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_27);
return x_28;
}
case 1:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_Lean_Expr_fvar___override(x_29);
x_31 = l_Lean_Meta_Simp_simpMatch___lam__0(x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_30);
return x_31;
}
case 2:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_1);
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = l_Lean_Expr_mvar___override(x_32);
x_34 = l_Lean_Meta_Simp_simpMatch___lam__0(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_33);
return x_34;
}
case 3:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
lean_dec(x_25);
x_36 = l_Lean_Expr_sort___override(x_35);
x_37 = l_Lean_Meta_Simp_simpMatch___lam__0(x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_36);
return x_37;
}
case 4:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
lean_inc(x_38);
x_39 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_Simp_simpMatch_spec__0___redArg(x_38, x_8, x_24);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
lean_dec(x_38);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_39, 0);
lean_dec(x_42);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_39, 0, x_44);
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_39, 1);
lean_inc(x_49);
lean_dec(x_39);
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
lean_dec(x_40);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_51 = l_Lean_Meta_Simp_simpMatchDiscrs_x3f(x_50, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Meta_Simp_simpMatchCore(x_38, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_53);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_38);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_51);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_51, 0);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
return x_51;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_52, 0);
lean_inc(x_58);
lean_dec(x_52);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_51, 0, x_59);
return x_51;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_dec(x_51);
x_61 = lean_ctor_get(x_52, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_62 = x_52;
} else {
 lean_dec_ref(x_52);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_61);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_38);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_51);
if (x_65 == 0)
{
return x_51;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_51, 0);
x_67 = lean_ctor_get(x_51, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_51);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
case 5:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_1);
x_69 = lean_ctor_get(x_25, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_25, 1);
lean_inc(x_70);
lean_dec(x_25);
x_71 = l_Lean_Expr_app___override(x_69, x_70);
x_72 = l_Lean_Meta_Simp_simpMatch___lam__0(x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_71);
return x_72;
}
case 6:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_1);
x_73 = lean_ctor_get(x_25, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_25, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_25, 2);
lean_inc(x_75);
x_76 = lean_ctor_get_uint8(x_25, sizeof(void*)*3 + 8);
lean_dec(x_25);
x_77 = l_Lean_Expr_lam___override(x_73, x_74, x_75, x_76);
x_78 = l_Lean_Meta_Simp_simpMatch___lam__0(x_77, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_77);
return x_78;
}
case 7:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_1);
x_79 = lean_ctor_get(x_25, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_25, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_25, 2);
lean_inc(x_81);
x_82 = lean_ctor_get_uint8(x_25, sizeof(void*)*3 + 8);
lean_dec(x_25);
x_83 = l_Lean_Expr_forallE___override(x_79, x_80, x_81, x_82);
x_84 = l_Lean_Meta_Simp_simpMatch___lam__0(x_83, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_83);
return x_84;
}
case 8:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_1);
x_85 = lean_ctor_get(x_25, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_25, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_25, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_25, 3);
lean_inc(x_88);
x_89 = lean_ctor_get_uint8(x_25, sizeof(void*)*4 + 8);
lean_dec(x_25);
x_90 = l_Lean_Expr_letE___override(x_85, x_86, x_87, x_88, x_89);
x_91 = l_Lean_Meta_Simp_simpMatch___lam__0(x_90, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_90);
return x_91;
}
case 9:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_1);
x_92 = lean_ctor_get(x_25, 0);
lean_inc(x_92);
lean_dec(x_25);
x_93 = l_Lean_Expr_lit___override(x_92);
x_94 = l_Lean_Meta_Simp_simpMatch___lam__0(x_93, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_93);
return x_94;
}
case 10:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_1);
x_95 = lean_ctor_get(x_25, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_25, 1);
lean_inc(x_96);
lean_dec(x_25);
x_97 = l_Lean_Expr_mdata___override(x_95, x_96);
x_98 = l_Lean_Meta_Simp_simpMatch___lam__0(x_97, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_97);
return x_98;
}
default: 
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_1);
x_99 = lean_ctor_get(x_25, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_25, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_25, 2);
lean_inc(x_101);
lean_dec(x_25);
x_102 = l_Lean_Expr_proj___override(x_99, x_100, x_101);
x_103 = l_Lean_Meta_Simp_simpMatch___lam__0(x_102, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_23);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_23, 0);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set_uint8(x_107, sizeof(void*)*2, x_12);
lean_ctor_set(x_23, 0, x_107);
if (lean_is_scalar(x_22)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_22;
}
lean_ctor_set(x_108, 0, x_23);
lean_ctor_set(x_108, 1, x_24);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_ctor_get(x_23, 0);
lean_inc(x_109);
lean_dec(x_23);
x_110 = lean_box(0);
x_111 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set_uint8(x_111, sizeof(void*)*2, x_12);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
if (lean_is_scalar(x_22)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_22;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_24);
return x_113;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_Simp_simpMatch_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_Simp_simpMatch_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_Simp_simpMatch_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_Simp_simpMatch_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_simpMatch___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewritePre_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
x_17 = lean_array_uget(x_3, x_5);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 4);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_mk_string_unchecked("pre", 3, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_21 = l_Lean_Meta_Simp_rewrite_x3f(x_1, x_18, x_19, x_20, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_box(0);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
lean_free_object(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_usize_add(x_5, x_29);
x_5 = x_30;
x_6 = x_27;
x_14 = x_24;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_23, 0, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_25);
lean_ctor_set(x_21, 0, x_35);
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
lean_dec(x_23);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_25);
lean_ctor_set(x_21, 0, x_39);
return x_21;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_21, 0);
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_21);
x_42 = lean_box(0);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; 
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_usize_of_nat(x_45);
x_47 = lean_usize_add(x_5, x_46);
x_5 = x_47;
x_6 = x_44;
x_14 = x_41;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_50 = x_40;
} else {
 lean_dec_ref(x_40);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_49);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_42);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_41);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_21);
if (x_55 == 0)
{
return x_21;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_21, 0);
x_57 = lean_ctor_get(x_21, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_21);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; size_t x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_4, 5);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_array_size(x_11);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_usize_of_nat(x_16);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewritePre_spec__0(x_2, x_1, x_11, x_15, x_17, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_18, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_31);
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_dec(x_18);
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_18);
if (x_35 == 0)
{
return x_18;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_18, 0);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_18);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewritePre_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewritePre_spec__0(x_1, x_15, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Meta_Simp_rewritePre(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewritePost_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
x_17 = lean_array_uget(x_3, x_5);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 4);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_mk_string_unchecked("post", 4, 4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_21 = l_Lean_Meta_Simp_rewrite_x3f(x_1, x_18, x_19, x_20, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_box(0);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
lean_free_object(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_usize_add(x_5, x_29);
x_5 = x_30;
x_6 = x_27;
x_14 = x_24;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_23, 0, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_25);
lean_ctor_set(x_21, 0, x_35);
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
lean_dec(x_23);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_25);
lean_ctor_set(x_21, 0, x_39);
return x_21;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_21, 0);
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_21);
x_42 = lean_box(0);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; 
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_usize_of_nat(x_45);
x_47 = lean_usize_add(x_5, x_46);
x_5 = x_47;
x_6 = x_44;
x_14 = x_41;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_50 = x_40;
} else {
 lean_dec_ref(x_40);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_49);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_42);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_41);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_21);
if (x_55 == 0)
{
return x_21;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_21, 0);
x_57 = lean_ctor_get(x_21, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_21);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePost(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; size_t x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_4, 5);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_array_size(x_11);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_usize_of_nat(x_16);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewritePost_spec__0(x_2, x_1, x_11, x_15, x_17, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_18, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_31);
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_dec(x_18);
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_18);
if (x_35 == 0)
{
return x_18;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_18, 0);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_18);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewritePost_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_rewritePost_spec__0(x_1, x_15, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePost___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Meta_Simp_rewritePost(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_drewritePre_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_4, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
x_16 = lean_array_uget(x_2, x_4);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 4);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_mk_string_unchecked("dpre", 4, 4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_20 = l_Lean_Meta_Simp_rewrite_x3f(x_1, x_17, x_18, x_19, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_box(0);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
lean_free_object(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_usize_of_nat(x_27);
x_29 = lean_usize_add(x_4, x_28);
x_4 = x_29;
x_5 = x_26;
x_13 = x_23;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_22, 0, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_20, 0, x_35);
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_22, 0);
lean_inc(x_36);
lean_dec(x_22);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_24);
lean_ctor_set(x_20, 0, x_40);
return x_20;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_20, 0);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_20);
x_43 = lean_box(0);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; 
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_usize_of_nat(x_46);
x_48 = lean_usize_add(x_4, x_47);
x_4 = x_48;
x_5 = x_45;
x_13 = x_42;
goto _start;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_50 = lean_ctor_get(x_41, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_51 = x_41;
} else {
 lean_dec_ref(x_41);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_51;
}
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_43);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_42);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_20);
if (x_57 == 0)
{
return x_20;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_20, 0);
x_59 = lean_ctor_get(x_20, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_20);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_drewritePre(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; size_t x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_3, 5);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_array_size(x_10);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_usize_of_nat(x_15);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_drewritePre_spec__0(x_1, x_10, x_14, x_16, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_17, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_30);
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_dec(x_17);
x_32 = lean_ctor_get(x_19, 0);
lean_inc(x_32);
lean_dec(x_19);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_17);
if (x_34 == 0)
{
return x_17;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_17, 0);
x_36 = lean_ctor_get(x_17, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_17);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_drewritePre_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_drewritePre_spec__0(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_drewritePost_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_4, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
x_16 = lean_array_uget(x_2, x_4);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 4);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_mk_string_unchecked("dpost", 5, 5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_20 = l_Lean_Meta_Simp_rewrite_x3f(x_1, x_17, x_18, x_19, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_box(0);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
lean_free_object(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_usize_of_nat(x_27);
x_29 = lean_usize_add(x_4, x_28);
x_4 = x_29;
x_5 = x_26;
x_13 = x_23;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_22, 0, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_20, 0, x_35);
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_22, 0);
lean_inc(x_36);
lean_dec(x_22);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_24);
lean_ctor_set(x_20, 0, x_40);
return x_20;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_20, 0);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_20);
x_43 = lean_box(0);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; 
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_usize_of_nat(x_46);
x_48 = lean_usize_add(x_4, x_47);
x_4 = x_48;
x_5 = x_45;
x_13 = x_42;
goto _start;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_50 = lean_ctor_get(x_41, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_51 = x_41;
} else {
 lean_dec_ref(x_41);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_51;
}
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_43);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_42);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_20);
if (x_57 == 0)
{
return x_20;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_20, 0);
x_59 = lean_ctor_get(x_20, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_20);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_drewritePost(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; size_t x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_3, 5);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_array_size(x_10);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_usize_of_nat(x_15);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_drewritePost_spec__0(x_1, x_10, x_14, x_16, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_17, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_30);
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_dec(x_17);
x_32 = lean_ctor_get(x_19, 0);
lean_inc(x_32);
lean_dec(x_19);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_17);
if (x_34 == 0)
{
return x_17;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_17, 0);
x_36 = lean_ctor_get(x_17, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_17);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_drewritePost_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_drewritePost_spec__0(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dpreDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Meta_Simp_drewritePre(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 2)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Meta_Simp_userPreDSimprocs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l_Lean_Meta_Simp_userPreDSimprocs(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_18;
}
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dpreDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_dpreDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dpostDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Meta_Simp_drewritePost(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 2)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Meta_Simp_userPostDSimprocs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l_Lean_Meta_Simp_userPostDSimprocs(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_18;
}
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dpostDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_dpostDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeGround(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_22; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_22 = lean_simp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = l_Lean_Expr_isTrue(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = lean_box(0);
lean_ctor_set(x_22, 0, x_28);
return x_22;
}
else
{
lean_object* x_29; 
lean_free_object(x_22);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = l_Lean_Meta_Simp_Result_getProof(x_24, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Meta_mkOfEqTrue(x_30, x_5, x_6, x_7, x_8, x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_inc(x_41);
x_16 = x_32;
x_17 = x_41;
x_18 = x_42;
goto block_21;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_32, 0);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_32);
lean_inc(x_44);
lean_inc(x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_16 = x_45;
x_17 = x_43;
x_18 = x_44;
goto block_21;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_29);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_29, 0);
x_48 = lean_ctor_get(x_29, 1);
lean_inc(x_48);
lean_inc(x_47);
x_16 = x_29;
x_17 = x_47;
x_18 = x_48;
goto block_21;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_29, 0);
x_50 = lean_ctor_get(x_29, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_29);
lean_inc(x_50);
lean_inc(x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_16 = x_51;
x_17 = x_49;
x_18 = x_50;
goto block_21;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = l_Lean_Expr_isTrue(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_52);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
else
{
lean_object* x_58; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_58 = l_Lean_Meta_Simp_Result_getProof(x_52, x_5, x_6, x_7, x_8, x_53);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Meta_mkOfEqTrue(x_59, x_5, x_6, x_7, x_8, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_62);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_61, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_69 = x_61;
} else {
 lean_dec_ref(x_61);
 x_69 = lean_box(0);
}
lean_inc(x_68);
lean_inc(x_67);
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
x_16 = x_70;
x_17 = x_67;
x_18 = x_68;
goto block_21;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_71 = lean_ctor_get(x_58, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_58, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_73 = x_58;
} else {
 lean_dec_ref(x_58);
 x_73 = lean_box(0);
}
lean_inc(x_72);
lean_inc(x_71);
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
x_16 = x_74;
x_17 = x_71;
x_18 = x_72;
goto block_21;
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_75 = !lean_is_exclusive(x_22);
if (x_75 == 0)
{
return x_22;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_22, 0);
x_77 = lean_ctor_get(x_22, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_22);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
block_15:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_dec(x_10);
return x_11;
}
}
block_21:
{
uint8_t x_19; 
x_19 = l_Lean_Exception_isInterrupt(x_17);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Exception_isRuntime(x_17);
lean_dec(x_17);
x_10 = x_18;
x_11 = x_16;
x_12 = x_20;
goto block_15;
}
else
{
lean_dec(x_17);
x_10 = x_18;
x_11 = x_16;
x_12 = x_19;
goto block_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_Simp_sevalGround_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_4, 5);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_ctor_get(x_4, 5);
lean_inc(x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_Simp_sevalGround_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_Simp_sevalGround_spec__0_spec__0___redArg(x_2, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Meta_Simp_sevalGround_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
lean_inc(x_1);
x_17 = l_Lean_Environment_find_x3f(x_14, x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_10);
x_18 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = lean_unbox(x_15);
x_21 = l_Lean_MessageData_ofConstName(x_1, x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_mk_string_unchecked("'", 1, 1);
x_24 = l_Lean_stringToMessageData(x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_Simp_sevalGround_spec__0_spec__0___redArg(x_25, x_5, x_6, x_7, x_8, x_13);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_1);
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
lean_ctor_set(x_10, 0, x_27);
return x_10;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_10, 0);
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_10);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
lean_inc(x_1);
x_33 = l_Lean_Environment_find_x3f(x_30, x_1, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_35 = l_Lean_stringToMessageData(x_34);
lean_dec(x_34);
x_36 = lean_unbox(x_31);
x_37 = l_Lean_MessageData_ofConstName(x_1, x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_mk_string_unchecked("'", 1, 1);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_Simp_sevalGround_spec__0_spec__0___redArg(x_41, x_5, x_6, x_7, x_8, x_29);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_1);
x_43 = lean_ctor_get(x_33, 0);
lean_inc(x_43);
lean_dec(x_33);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_29);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_sevalGround_spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_17 = lean_array_uget(x_3, x_5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_17);
x_18 = l_Lean_Meta_isRflTheorem(x_17, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_mk_empty_array_with_capacity(x_21);
x_23 = lean_box(0);
lean_inc(x_17);
x_24 = l_Lean_Expr_const___override(x_17, x_23);
x_25 = lean_unsigned_to_nat(1000u);
x_26 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_15);
lean_ctor_set_uint8(x_26, sizeof(void*)*1 + 1, x_1);
lean_inc(x_22);
x_27 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 1, x_1);
x_28 = lean_unbox(x_19);
lean_dec(x_19);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 2, x_28);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_29 = l_Lean_Meta_Simp_tryTheorem_x3f(x_2, x_27, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
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
x_33 = lean_box(0);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; 
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_usize_of_nat(x_36);
x_38 = lean_usize_add(x_5, x_37);
x_5 = x_38;
x_6 = x_35;
x_14 = x_31;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_41 = x_30;
} else {
 lean_dec_ref(x_30);
 x_41 = lean_box(0);
}
x_48 = lean_mk_string_unchecked("Meta", 4, 4);
x_49 = lean_mk_string_unchecked("Tactic", 6, 6);
x_50 = lean_mk_string_unchecked("simp", 4, 4);
x_51 = lean_mk_string_unchecked("ground", 6, 6);
x_52 = l_Lean_Name_mkStr4(x_48, x_49, x_50, x_51);
lean_inc(x_52);
x_53 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_52, x_12, x_31);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_52);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_42 = x_56;
goto block_47;
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_58 = lean_ctor_get(x_53, 1);
x_59 = lean_ctor_get(x_53, 0);
lean_dec(x_59);
x_60 = lean_mk_string_unchecked("unfolded, ", 10, 10);
x_61 = l_Lean_stringToMessageData(x_60);
lean_dec(x_60);
x_62 = l_Lean_MessageData_ofExpr(x_2);
lean_ctor_set_tag(x_53, 7);
lean_ctor_set(x_53, 1, x_62);
lean_ctor_set(x_53, 0, x_61);
x_63 = lean_mk_string_unchecked(" => ", 4, 4);
x_64 = l_Lean_stringToMessageData(x_63);
lean_dec(x_63);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_53);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_ctor_get(x_40, 0);
lean_inc(x_66);
x_67 = l_Lean_MessageData_ofExpr(x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_mk_string_unchecked("", 0, 0);
x_70 = l_Lean_stringToMessageData(x_69);
lean_dec(x_69);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_52, x_71, x_10, x_11, x_12, x_13, x_58);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_42 = x_73;
goto block_47;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_74 = lean_ctor_get(x_53, 1);
lean_inc(x_74);
lean_dec(x_53);
x_75 = lean_mk_string_unchecked("unfolded, ", 10, 10);
x_76 = l_Lean_stringToMessageData(x_75);
lean_dec(x_75);
x_77 = l_Lean_MessageData_ofExpr(x_2);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_mk_string_unchecked(" => ", 4, 4);
x_80 = l_Lean_stringToMessageData(x_79);
lean_dec(x_79);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_ctor_get(x_40, 0);
lean_inc(x_82);
x_83 = l_Lean_MessageData_ofExpr(x_82);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_mk_string_unchecked("", 0, 0);
x_86 = l_Lean_stringToMessageData(x_85);
lean_dec(x_85);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_52, x_87, x_10, x_11, x_12, x_13, x_74);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_42 = x_89;
goto block_47;
}
}
block_47:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_40);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_33);
if (lean_is_scalar(x_32)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_32;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_29);
if (x_90 == 0)
{
return x_29;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_29, 0);
x_92 = lean_ctor_get(x_29, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_29);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_18);
if (x_94 == 0)
{
return x_18;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_18, 0);
x_96 = lean_ctor_get(x_18, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_18);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_22; 
x_22 = l_Lean_getConstInfo___at___Lean_Meta_Simp_sevalGround_spec__0(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_86; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_86 = l_Lean_ConstantInfo_hasValue(x_23, x_4);
if (x_86 == 0)
{
x_26 = x_86;
goto block_85;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = l_Lean_ConstantInfo_levelParams(x_23);
x_88 = l_List_lengthTR(lean_box(0), x_87);
lean_dec(x_87);
x_89 = l_List_lengthTR(lean_box(0), x_2);
x_90 = lean_nat_dec_eq(x_88, x_89);
lean_dec(x_89);
lean_dec(x_88);
x_26 = x_90;
goto block_85;
}
block_85:
{
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_23);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
if (lean_is_scalar(x_25)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_25;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_25);
x_30 = l_Lean_Core_instantiateValueLevelParams(x_23, x_2, x_11, x_12, x_24);
lean_dec(x_23);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_mk_string_unchecked("Meta", 4, 4);
x_34 = lean_mk_string_unchecked("Tactic", 6, 6);
x_35 = lean_mk_string_unchecked("simp", 4, 4);
x_36 = lean_mk_string_unchecked("ground", 6, 6);
x_37 = l_Lean_Name_mkStr4(x_33, x_34, x_35, x_36);
lean_inc(x_37);
x_38 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_37, x_11, x_32);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
x_42 = l_Lean_Expr_getAppNumArgs(x_3);
x_43 = lean_mk_empty_array_with_capacity(x_42);
lean_dec(x_42);
lean_inc(x_3);
x_44 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_3, x_43);
x_45 = l_Lean_Expr_betaRev(x_31, x_44, x_26, x_4);
lean_dec(x_44);
x_46 = lean_unbox(x_40);
lean_dec(x_40);
if (x_46 == 0)
{
lean_free_object(x_38);
lean_dec(x_37);
lean_dec(x_3);
x_14 = x_26;
x_15 = x_45;
x_16 = x_41;
goto block_21;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_47 = lean_mk_string_unchecked("delta, ", 7, 7);
x_48 = l_Lean_stringToMessageData(x_47);
lean_dec(x_47);
x_49 = l_Lean_MessageData_ofExpr(x_3);
lean_ctor_set_tag(x_38, 7);
lean_ctor_set(x_38, 1, x_49);
lean_ctor_set(x_38, 0, x_48);
x_50 = lean_mk_string_unchecked(" => ", 4, 4);
x_51 = l_Lean_stringToMessageData(x_50);
lean_dec(x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_38);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_45);
x_53 = l_Lean_MessageData_ofExpr(x_45);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_mk_string_unchecked("", 0, 0);
x_56 = l_Lean_stringToMessageData(x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_37, x_57, x_9, x_10, x_11, x_12, x_41);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_14 = x_26;
x_15 = x_45;
x_16 = x_59;
goto block_21;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_60 = lean_ctor_get(x_38, 0);
x_61 = lean_ctor_get(x_38, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_38);
x_62 = l_Lean_Expr_getAppNumArgs(x_3);
x_63 = lean_mk_empty_array_with_capacity(x_62);
lean_dec(x_62);
lean_inc(x_3);
x_64 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_3, x_63);
x_65 = l_Lean_Expr_betaRev(x_31, x_64, x_26, x_4);
lean_dec(x_64);
x_66 = lean_unbox(x_60);
lean_dec(x_60);
if (x_66 == 0)
{
lean_dec(x_37);
lean_dec(x_3);
x_14 = x_26;
x_15 = x_65;
x_16 = x_61;
goto block_21;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_67 = lean_mk_string_unchecked("delta, ", 7, 7);
x_68 = l_Lean_stringToMessageData(x_67);
lean_dec(x_67);
x_69 = l_Lean_MessageData_ofExpr(x_3);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_mk_string_unchecked(" => ", 4, 4);
x_72 = l_Lean_stringToMessageData(x_71);
lean_dec(x_71);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
lean_inc(x_65);
x_74 = l_Lean_MessageData_ofExpr(x_65);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_mk_string_unchecked("", 0, 0);
x_77 = l_Lean_stringToMessageData(x_76);
lean_dec(x_76);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_37, x_78, x_9, x_10, x_11, x_12, x_61);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_14 = x_26;
x_15 = x_65;
x_16 = x_80;
goto block_21;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_30);
if (x_81 == 0)
{
return x_30;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_30, 0);
x_83 = lean_ctor_get(x_30, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_30);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_3);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_22);
if (x_91 == 0)
{
return x_22;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_22, 0);
x_93 = lean_ctor_get(x_22, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_22);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
block_21:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_14);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_14; 
x_14 = l_Lean_Expr_hasExprMVar(x_1);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Expr_hasFVar(x_1);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(1);
x_20 = lean_ctor_get(x_3, 5);
lean_inc(x_20);
lean_inc(x_17);
x_21 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_21, 0, x_17);
x_22 = lean_unbox(x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_22);
lean_ctor_set_uint8(x_21, sizeof(void*)*1 + 1, x_15);
x_23 = l_Lean_Meta_SimpTheoremsArray_isErased(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_inc(x_17);
x_24 = l_Lean_Meta_isMatcher___at___Lean_Meta_Simp_mkCongrSimp_x3f_spec__1___redArg(x_17, x_8, x_9);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; uint8_t x_48; uint64_t x_49; lean_object* x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint8_t x_54; uint64_t x_55; uint64_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(1);
x_29 = lean_ctor_get(x_5, 0);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_29, 0);
x_31 = lean_ctor_get_uint8(x_29, 1);
x_32 = lean_ctor_get_uint8(x_29, 2);
x_33 = lean_ctor_get_uint8(x_29, 3);
x_34 = lean_ctor_get_uint8(x_29, 4);
x_35 = lean_ctor_get_uint8(x_29, 5);
x_36 = lean_ctor_get_uint8(x_29, 6);
x_37 = lean_ctor_get_uint8(x_29, 7);
x_38 = lean_ctor_get_uint8(x_29, 8);
x_39 = lean_ctor_get_uint8(x_29, 10);
x_40 = lean_ctor_get_uint8(x_29, 11);
x_41 = lean_ctor_get_uint8(x_29, 12);
x_42 = lean_ctor_get_uint8(x_29, 13);
x_43 = lean_ctor_get_uint8(x_29, 14);
x_44 = lean_ctor_get_uint8(x_29, 15);
x_45 = lean_ctor_get_uint8(x_29, 16);
x_46 = lean_ctor_get_uint8(x_29, 17);
lean_dec(x_29);
x_47 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_47, 0, x_30);
lean_ctor_set_uint8(x_47, 1, x_31);
lean_ctor_set_uint8(x_47, 2, x_32);
lean_ctor_set_uint8(x_47, 3, x_33);
lean_ctor_set_uint8(x_47, 4, x_34);
lean_ctor_set_uint8(x_47, 5, x_35);
lean_ctor_set_uint8(x_47, 6, x_36);
lean_ctor_set_uint8(x_47, 7, x_37);
lean_ctor_set_uint8(x_47, 8, x_38);
x_48 = lean_unbox(x_28);
lean_ctor_set_uint8(x_47, 9, x_48);
lean_ctor_set_uint8(x_47, 10, x_39);
lean_ctor_set_uint8(x_47, 11, x_40);
lean_ctor_set_uint8(x_47, 12, x_41);
lean_ctor_set_uint8(x_47, 13, x_42);
lean_ctor_set_uint8(x_47, 14, x_43);
lean_ctor_set_uint8(x_47, 15, x_44);
lean_ctor_set_uint8(x_47, 16, x_45);
lean_ctor_set_uint8(x_47, 17, x_46);
x_49 = lean_ctor_get_uint64(x_5, sizeof(void*)*7);
x_50 = lean_unsigned_to_nat(2u);
x_51 = lean_uint64_of_nat(x_50);
x_52 = lean_uint64_shift_right(x_49, x_51);
x_53 = lean_uint64_shift_left(x_52, x_51);
x_54 = lean_unbox(x_28);
x_55 = l_Lean_Meta_TransparencyMode_toUInt64(x_54);
x_56 = lean_uint64_lor(x_53, x_55);
x_57 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 8);
x_58 = lean_ctor_get(x_5, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_5, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_5, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_5, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_5, 5);
lean_inc(x_62);
x_63 = lean_ctor_get(x_5, 6);
lean_inc(x_63);
x_64 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_65 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
x_66 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_66, 0, x_47);
lean_ctor_set(x_66, 1, x_58);
lean_ctor_set(x_66, 2, x_59);
lean_ctor_set(x_66, 3, x_60);
lean_ctor_set(x_66, 4, x_61);
lean_ctor_set(x_66, 5, x_62);
lean_ctor_set(x_66, 6, x_63);
lean_ctor_set_uint64(x_66, sizeof(void*)*7, x_56);
lean_ctor_set_uint8(x_66, sizeof(void*)*7 + 8, x_57);
lean_ctor_set_uint8(x_66, sizeof(void*)*7 + 9, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*7 + 10, x_65);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_17);
x_67 = l_Lean_Meta_getEqnsFor_x3f(x_17, x_66, x_6, x_7, x_8, x_27);
lean_dec(x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_Expr_isConst(x_1);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_71 = lean_box(0);
x_72 = lean_unbox(x_25);
lean_dec(x_25);
x_73 = l_Lean_Meta_Simp_sevalGround___lam__0(x_17, x_18, x_1, x_72, x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_73;
}
else
{
lean_object* x_74; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_74 = lean_infer_type(x_1, x_5, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_77 = l_Lean_Meta_whnfD(x_75, x_5, x_6, x_7, x_8, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 7)
{
uint8_t x_79; 
lean_dec(x_78);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_77);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_77, 0);
lean_dec(x_80);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_77, 0, x_82);
return x_77;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
lean_dec(x_77);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; 
lean_dec(x_78);
x_87 = lean_ctor_get(x_77, 1);
lean_inc(x_87);
lean_dec(x_77);
x_88 = lean_box(0);
x_89 = lean_unbox(x_25);
lean_dec(x_25);
x_90 = l_Lean_Meta_Simp_sevalGround___lam__0(x_17, x_18, x_1, x_89, x_88, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_87);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_90;
}
}
else
{
uint8_t x_91; 
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_77);
if (x_91 == 0)
{
return x_77;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_77, 0);
x_93 = lean_ctor_get(x_77, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_77);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_74);
if (x_95 == 0)
{
return x_74;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_74, 0);
x_97 = lean_ctor_get(x_74, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_74);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
else
{
lean_object* x_99; uint8_t x_100; 
lean_dec(x_18);
lean_dec(x_17);
x_99 = lean_ctor_get(x_67, 1);
lean_inc(x_99);
lean_dec(x_67);
x_100 = !lean_is_exclusive(x_68);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; size_t x_105; lean_object* x_106; size_t x_107; uint8_t x_108; lean_object* x_109; 
x_101 = lean_ctor_get(x_68, 0);
x_102 = lean_box(0);
x_103 = lean_box(0);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_array_size(x_101);
x_106 = lean_unsigned_to_nat(0u);
x_107 = lean_usize_of_nat(x_106);
x_108 = lean_unbox(x_25);
lean_dec(x_25);
x_109 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_sevalGround_spec__2(x_108, x_1, x_101, x_105, x_107, x_104, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_99);
lean_dec(x_101);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec(x_110);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_109);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_109, 0);
lean_dec(x_113);
x_114 = lean_box(0);
lean_ctor_set_tag(x_68, 2);
lean_ctor_set(x_68, 0, x_114);
lean_ctor_set(x_109, 0, x_68);
return x_109;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
lean_dec(x_109);
x_116 = lean_box(0);
lean_ctor_set_tag(x_68, 2);
lean_ctor_set(x_68, 0, x_116);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_68);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
else
{
uint8_t x_118; 
lean_free_object(x_68);
x_118 = !lean_is_exclusive(x_109);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_109, 0);
lean_dec(x_119);
x_120 = lean_ctor_get(x_111, 0);
lean_inc(x_120);
lean_dec(x_111);
lean_ctor_set(x_109, 0, x_120);
return x_109;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_109, 1);
lean_inc(x_121);
lean_dec(x_109);
x_122 = lean_ctor_get(x_111, 0);
lean_inc(x_122);
lean_dec(x_111);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_free_object(x_68);
x_124 = !lean_is_exclusive(x_109);
if (x_124 == 0)
{
return x_109;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_109, 0);
x_126 = lean_ctor_get(x_109, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_109);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; size_t x_132; lean_object* x_133; size_t x_134; uint8_t x_135; lean_object* x_136; 
x_128 = lean_ctor_get(x_68, 0);
lean_inc(x_128);
lean_dec(x_68);
x_129 = lean_box(0);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_array_size(x_128);
x_133 = lean_unsigned_to_nat(0u);
x_134 = lean_usize_of_nat(x_133);
x_135 = lean_unbox(x_25);
lean_dec(x_25);
x_136 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_sevalGround_spec__2(x_135, x_1, x_128, x_132, x_134, x_131, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_99);
lean_dec(x_128);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec(x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_140 = x_136;
} else {
 lean_dec_ref(x_136);
 x_140 = lean_box(0);
}
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_142, 0, x_141);
if (lean_is_scalar(x_140)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_140;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_139);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_136, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_145 = x_136;
} else {
 lean_dec_ref(x_136);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_138, 0);
lean_inc(x_146);
lean_dec(x_138);
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_144);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_136, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_136, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_150 = x_136;
} else {
 lean_dec_ref(x_136);
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
}
}
else
{
uint8_t x_152; 
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_67);
if (x_152 == 0)
{
return x_67;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_67, 0);
x_154 = lean_ctor_get(x_67, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_67);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_24);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_24, 0);
lean_dec(x_157);
x_158 = lean_box(0);
x_159 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_24, 0, x_159);
return x_24;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_24, 1);
lean_inc(x_160);
lean_dec(x_24);
x_161 = lean_box(0);
x_162 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_162, 0, x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_160);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_164 = lean_box(0);
x_165 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_9);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_167 = lean_box(0);
x_168 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_168, 0, x_167);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_9);
return x_169;
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
goto block_13;
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
goto block_13;
}
block_13:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_Simp_sevalGround_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_Simp_sevalGround_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_Simp_sevalGround_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_Simp_sevalGround_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Meta_Simp_sevalGround_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_getConstInfo___at___Lean_Meta_Simp_sevalGround_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_sevalGround_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_sevalGround_spec__2(x_15, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Meta_Simp_sevalGround___lam__0(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preSEval___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Meta_Simp_simpMatch(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 2)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Meta_Simp_userPreSimprocs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Meta_Simp_userPreSimprocs(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_Simp_mkEqTransResultStep(x_17, x_20, x_6, x_7, x_8, x_9, x_21);
return x_22;
}
else
{
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_19;
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preSEval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Meta_Simp_rewritePre(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 2)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Meta_Simp_preSEval___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Meta_Simp_preSEval___lam__0(x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_Simp_mkEqTransResultStep(x_19, x_22, x_6, x_7, x_8, x_9, x_23);
return x_24;
}
else
{
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_21;
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preSEval___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_preSEval___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preSEval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_preSEval(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postSEval___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Meta_Simp_userPostSimprocs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 2)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Meta_Simp_sevalGround(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Meta_Simp_sevalGround(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_Simp_mkEqTransResultStep(x_17, x_20, x_6, x_7, x_8, x_9, x_21);
return x_22;
}
else
{
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_19;
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postSEval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Meta_Simp_rewritePost(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 2)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Meta_Simp_postSEval___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Meta_Simp_postSEval___lam__0(x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_Simp_mkEqTransResultStep(x_19, x_22, x_6, x_7, x_8, x_9, x_23);
return x_24;
}
else
{
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_21;
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postSEval___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_postSEval___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postSEval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_postSEval(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSEvalMethods(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Meta_Simp_getSEvalSimprocs(x_1, x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_mk_empty_array_with_capacity(x_7);
x_9 = lean_array_push(x_8, x_6);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_preSEval___boxed), 10, 1);
lean_closure_set(x_10, 0, x_9);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_postSEval___boxed), 10, 1);
lean_closure_set(x_11, 0, x_9);
lean_inc(x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_dpreDefault___boxed), 10, 1);
lean_closure_set(x_12, 0, x_9);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_dpostDefault___boxed), 10, 1);
lean_closure_set(x_13, 0, x_9);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_dischargeGround), 9, 0);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set(x_16, 4, x_14);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_17);
lean_ctor_set(x_4, 0, x_16);
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_mk_empty_array_with_capacity(x_20);
x_22 = lean_array_push(x_21, x_18);
lean_inc(x_22);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_preSEval___boxed), 10, 1);
lean_closure_set(x_23, 0, x_22);
lean_inc(x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_postSEval___boxed), 10, 1);
lean_closure_set(x_24, 0, x_22);
lean_inc(x_22);
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_dpreDefault___boxed), 10, 1);
lean_closure_set(x_25, 0, x_22);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_dpostDefault___boxed), 10, 1);
lean_closure_set(x_26, 0, x_22);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_dischargeGround), 9, 0);
x_28 = lean_box(1);
x_29 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 3, x_26);
lean_ctor_set(x_29, 4, x_27);
x_30 = lean_unbox(x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*5, x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_19);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSEvalMethods___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_mkSEvalMethods(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSEvalContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_6 = l_Lean_Meta_getSEvalTheorems(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Meta_getSimpCongrTheorems(x_3, x_4, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(100000u);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_box(0);
x_15 = lean_box(1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
x_18 = lean_unbox(x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_18);
x_19 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 1, x_19);
x_20 = lean_unbox(x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 2, x_20);
x_21 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 3, x_21);
x_22 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 4, x_22);
x_23 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 5, x_23);
x_24 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 6, x_24);
x_25 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 7, x_25);
x_26 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 8, x_26);
x_27 = lean_unbox(x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 9, x_27);
x_28 = lean_unbox(x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 10, x_28);
x_29 = lean_unbox(x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 11, x_29);
x_30 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 12, x_30);
x_31 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 13, x_31);
x_32 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 14, x_32);
x_33 = lean_unbox(x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 15, x_33);
x_34 = lean_unbox(x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 16, x_34);
x_35 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 17, x_35);
x_36 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 18, x_36);
x_37 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 19, x_37);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_mk_empty_array_with_capacity(x_38);
x_40 = lean_array_push(x_39, x_7);
x_41 = l_Lean_Meta_Simp_mkContext(x_17, x_40, x_10, x_1, x_2, x_3, x_4, x_11);
return x_41;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSEvalContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Simp_mkSEvalContext(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_seval___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_st_ref_take(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 4);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set(x_12, 3, x_10);
lean_ctor_set(x_12, 4, x_11);
x_13 = lean_st_ref_set(x_1, x_12, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_seval___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_8 = l_Lean_Meta_Simp_mkSEvalMethods(x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_Simp_mkSEvalContext(x_3, x_4, x_5, x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_2, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_2, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_st_ref_take(x_2, x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_box(1);
x_26 = lean_unsigned_to_nat(8u);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_nat_shiftl(x_26, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = l_Nat_nextPowerOfTwo(x_31);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = lean_mk_array(x_32, x_33);
lean_ctor_set(x_21, 1, x_34);
lean_ctor_set(x_21, 0, x_27);
x_35 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_35);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_21);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_unbox(x_25);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_38);
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_17, 1, x_27);
lean_ctor_set(x_17, 0, x_40);
x_41 = lean_ctor_get(x_23, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_23, 4);
lean_inc(x_42);
lean_dec(x_23);
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set(x_43, 2, x_17);
lean_ctor_set(x_43, 3, x_41);
lean_ctor_set(x_43, 4, x_42);
x_44 = lean_st_ref_set(x_2, x_43, x_24);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_15, 0);
lean_inc(x_46);
lean_dec(x_15);
x_47 = lean_ctor_get(x_19, 2);
lean_inc(x_47);
lean_dec(x_19);
lean_inc(x_2);
x_48 = lean_simp(x_1, x_9, x_12, x_2, x_3, x_4, x_5, x_6, x_45);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_49);
x_52 = l_Lean_Meta_Simp_seval___redArg___lam__0(x_2, x_46, x_47, x_51, x_50);
lean_dec(x_51);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set(x_52, 0, x_49);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_48, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_dec(x_48);
x_59 = lean_box(0);
x_60 = l_Lean_Meta_Simp_seval___redArg___lam__0(x_2, x_46, x_47, x_59, x_58);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 0, x_57);
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_65 = lean_ctor_get(x_21, 0);
x_66 = lean_ctor_get(x_21, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_21);
x_67 = lean_box(1);
x_68 = lean_unsigned_to_nat(8u);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_unsigned_to_nat(2u);
x_71 = lean_nat_shiftl(x_68, x_70);
x_72 = lean_unsigned_to_nat(3u);
x_73 = lean_nat_div(x_71, x_72);
lean_dec(x_71);
x_74 = l_Nat_nextPowerOfTwo(x_73);
lean_dec(x_73);
x_75 = lean_box(0);
x_76 = lean_mk_array(x_74, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_69);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_78);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_unbox(x_67);
lean_ctor_set_uint8(x_80, sizeof(void*)*2, x_81);
x_82 = lean_ctor_get(x_65, 1);
lean_inc(x_82);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_17, 1, x_69);
lean_ctor_set(x_17, 0, x_83);
x_84 = lean_ctor_get(x_65, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_65, 4);
lean_inc(x_85);
lean_dec(x_65);
x_86 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_82);
lean_ctor_set(x_86, 2, x_17);
lean_ctor_set(x_86, 3, x_84);
lean_ctor_set(x_86, 4, x_85);
x_87 = lean_st_ref_set(x_2, x_86, x_66);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_ctor_get(x_15, 0);
lean_inc(x_89);
lean_dec(x_15);
x_90 = lean_ctor_get(x_19, 2);
lean_inc(x_90);
lean_dec(x_19);
lean_inc(x_2);
x_91 = lean_simp(x_1, x_9, x_12, x_2, x_3, x_4, x_5, x_6, x_88);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
lean_inc(x_92);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_92);
x_95 = l_Lean_Meta_Simp_seval___redArg___lam__0(x_2, x_89, x_90, x_94, x_93);
lean_dec(x_94);
lean_dec(x_2);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_92);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_91, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_91, 1);
lean_inc(x_100);
lean_dec(x_91);
x_101 = lean_box(0);
x_102 = l_Lean_Meta_Simp_seval___redArg___lam__0(x_2, x_89, x_90, x_101, x_100);
lean_dec(x_2);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
 lean_ctor_set_tag(x_105, 1);
}
lean_ctor_set(x_105, 0, x_99);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_106 = lean_ctor_get(x_17, 0);
x_107 = lean_ctor_get(x_17, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_17);
x_108 = lean_st_ref_take(x_2, x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
x_112 = lean_box(1);
x_113 = lean_unsigned_to_nat(8u);
x_114 = lean_unsigned_to_nat(0u);
x_115 = lean_unsigned_to_nat(2u);
x_116 = lean_nat_shiftl(x_113, x_115);
x_117 = lean_unsigned_to_nat(3u);
x_118 = lean_nat_div(x_116, x_117);
lean_dec(x_116);
x_119 = l_Nat_nextPowerOfTwo(x_118);
lean_dec(x_118);
x_120 = lean_box(0);
x_121 = lean_mk_array(x_119, x_120);
if (lean_is_scalar(x_111)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_111;
}
lean_ctor_set(x_122, 0, x_114);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_123);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_unbox(x_112);
lean_ctor_set_uint8(x_125, sizeof(void*)*2, x_126);
x_127 = lean_ctor_get(x_109, 1);
lean_inc(x_127);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_123);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_114);
x_130 = lean_ctor_get(x_109, 3);
lean_inc(x_130);
x_131 = lean_ctor_get(x_109, 4);
lean_inc(x_131);
lean_dec(x_109);
x_132 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_132, 0, x_125);
lean_ctor_set(x_132, 1, x_127);
lean_ctor_set(x_132, 2, x_129);
lean_ctor_set(x_132, 3, x_130);
lean_ctor_set(x_132, 4, x_131);
x_133 = lean_st_ref_set(x_2, x_132, x_110);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_ctor_get(x_15, 0);
lean_inc(x_135);
lean_dec(x_15);
x_136 = lean_ctor_get(x_106, 2);
lean_inc(x_136);
lean_dec(x_106);
lean_inc(x_2);
x_137 = lean_simp(x_1, x_9, x_12, x_2, x_3, x_4, x_5, x_6, x_134);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
lean_inc(x_138);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_138);
x_141 = l_Lean_Meta_Simp_seval___redArg___lam__0(x_2, x_135, x_136, x_140, x_139);
lean_dec(x_140);
lean_dec(x_2);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_138);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_145 = lean_ctor_get(x_137, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_137, 1);
lean_inc(x_146);
lean_dec(x_137);
x_147 = lean_box(0);
x_148 = l_Lean_Meta_Simp_seval___redArg___lam__0(x_2, x_135, x_136, x_147, x_146);
lean_dec(x_2);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
 lean_ctor_set_tag(x_151, 1);
}
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_seval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_seval___redArg(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_seval___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Simp_seval___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_seval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_seval(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_mk_string_unchecked("seval: ", 7, 7);
x_13 = l_Lean_stringToMessageData(x_12);
lean_dec(x_12);
x_14 = l_Lean_MessageData_ofExpr(x_1);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_mk_string_unchecked(" => ", 4, 4);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Exception_toMessageData(x_11);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked("", 0, 0);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_10);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
lean_dec(x_2);
x_26 = lean_mk_string_unchecked("seval: ", 7, 7);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = l_Lean_MessageData_ofExpr(x_1);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_mk_string_unchecked(" => ", 4, 4);
x_31 = l_Lean_stringToMessageData(x_30);
lean_dec(x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
x_34 = l_Lean_MessageData_ofExpr(x_33);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_mk_string_unchecked("", 0, 0);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_10);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_10 = l_Lean_Meta_Simp_getConfig___redArg(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_18 = lean_ctor_get_uint8(x_11, sizeof(void*)*2 + 14);
lean_dec(x_11);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = l_Lean_Expr_hasExprMVar(x_1);
if (x_22 == 0)
{
if (x_18 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_17;
}
else
{
uint8_t x_23; 
x_23 = l_Lean_Expr_hasFVar(x_1);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_13);
x_24 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_24) == 4)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_3, 5);
lean_inc(x_26);
lean_inc(x_25);
x_27 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_18);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 1, x_23);
x_28 = l_Lean_Meta_SimpTheoremsArray_isErased(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = l_Lean_Meta_isMatcher___at___Lean_Meta_Simp_mkCongrSimp_x3f_spec__1___redArg(x_25, x_8, x_12);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
lean_inc(x_1);
x_33 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_simpGround___lam__0___boxed), 10, 1);
lean_closure_set(x_33, 0, x_1);
x_34 = lean_mk_string_unchecked("Meta", 4, 4);
x_35 = lean_mk_string_unchecked("Tactic", 6, 6);
x_36 = lean_mk_string_unchecked("simp", 4, 4);
x_37 = lean_mk_string_unchecked("ground", 6, 6);
x_38 = l_Lean_Name_mkStr4(x_34, x_35, x_36, x_37);
x_39 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_seval___boxed), 9, 1);
lean_closure_set(x_39, 0, x_1);
x_40 = lean_mk_string_unchecked("", 0, 0);
x_41 = l_Lean_withTraceNode___at___Lean_Meta_Simp_discharge_x3f_x27_spec__2___redArg(x_38, x_33, x_39, x_18, x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_41);
if (x_49 == 0)
{
return x_41;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_41, 0);
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_41);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_29);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_29, 0);
lean_dec(x_54);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_29, 0, x_56);
return x_29;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_29, 1);
lean_inc(x_57);
lean_dec(x_29);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_12);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_12);
return x_66;
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
goto block_17;
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
goto block_17;
}
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
if (lean_is_scalar(x_13)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_13;
}
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_simpGround___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preDefault___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_31; uint8_t x_32; 
x_23 = l_Lean_Meta_Simp_getConfig___redArg(x_3, x_9);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_31 = lean_ctor_get_uint8(x_24, sizeof(void*)*2 + 9);
lean_dec(x_24);
if (x_31 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_261 = lean_box(0);
x_262 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_262, 0, x_261);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_25);
return x_263;
}
else
{
uint8_t x_264; 
x_264 = l_Lean_Expr_hasFVar(x_1);
if (x_264 == 0)
{
uint8_t x_265; 
x_265 = l_Lean_Expr_hasMVar(x_1);
x_32 = x_265;
goto block_260;
}
else
{
x_32 = x_264;
goto block_260;
}
}
block_16:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
lean_dec(x_10);
return x_11;
}
}
block_22:
{
uint8_t x_20; 
x_20 = l_Lean_Exception_isInterrupt(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Exception_isRuntime(x_18);
lean_dec(x_18);
x_10 = x_19;
x_11 = x_17;
x_12 = x_21;
goto block_16;
}
else
{
lean_dec(x_18);
x_10 = x_19;
x_11 = x_17;
x_12 = x_20;
goto block_16;
}
}
block_30:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
if (lean_is_scalar(x_26)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_26;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
block_260:
{
if (x_32 == 0)
{
uint8_t x_33; 
lean_inc(x_1);
x_33 = l_Lean_Expr_isTrue(x_1);
if (x_33 == 0)
{
uint8_t x_34; 
lean_inc(x_1);
x_34 = l_Lean_Expr_isFalse(x_1);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_26);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_35 = l_Lean_Meta_mkDecide(x_1, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; uint64_t x_59; lean_object* x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint8_t x_64; uint64_t x_65; uint64_t x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_box(1);
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
x_58 = lean_unbox(x_38);
lean_ctor_set_uint8(x_57, 9, x_58);
lean_ctor_set_uint8(x_57, 10, x_49);
lean_ctor_set_uint8(x_57, 11, x_50);
lean_ctor_set_uint8(x_57, 12, x_51);
lean_ctor_set_uint8(x_57, 13, x_52);
lean_ctor_set_uint8(x_57, 14, x_53);
lean_ctor_set_uint8(x_57, 15, x_54);
lean_ctor_set_uint8(x_57, 16, x_55);
lean_ctor_set_uint8(x_57, 17, x_56);
x_59 = lean_ctor_get_uint64(x_5, sizeof(void*)*7);
x_60 = lean_unsigned_to_nat(2u);
x_61 = lean_uint64_of_nat(x_60);
x_62 = lean_uint64_shift_right(x_59, x_61);
x_63 = lean_uint64_shift_left(x_62, x_61);
x_64 = lean_unbox(x_38);
x_65 = l_Lean_Meta_TransparencyMode_toUInt64(x_64);
x_66 = lean_uint64_lor(x_63, x_65);
x_67 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 8);
x_68 = lean_ctor_get(x_5, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_5, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_5, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_5, 4);
lean_inc(x_71);
x_72 = lean_ctor_get(x_5, 5);
lean_inc(x_72);
x_73 = lean_ctor_get(x_5, 6);
lean_inc(x_73);
x_74 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_75 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
x_76 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_76, 0, x_57);
lean_ctor_set(x_76, 1, x_68);
lean_ctor_set(x_76, 2, x_69);
lean_ctor_set(x_76, 3, x_70);
lean_ctor_set(x_76, 4, x_71);
lean_ctor_set(x_76, 5, x_72);
lean_ctor_set(x_76, 6, x_73);
lean_ctor_set_uint64(x_76, sizeof(void*)*7, x_66);
lean_ctor_set_uint8(x_76, sizeof(void*)*7 + 8, x_67);
lean_ctor_set_uint8(x_76, sizeof(void*)*7 + 9, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*7 + 10, x_75);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_36);
x_77 = lean_whnf(x_36, x_76, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
x_81 = lean_mk_string_unchecked("Bool", 4, 4);
x_82 = lean_mk_string_unchecked("true", 4, 4);
lean_inc(x_81);
x_83 = l_Lean_Name_mkStr2(x_81, x_82);
x_84 = l_Lean_Expr_isConstOf(x_79, x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_dec(x_83);
x_85 = lean_mk_string_unchecked("false", 5, 5);
x_86 = l_Lean_Name_mkStr2(x_81, x_85);
x_87 = l_Lean_Expr_isConstOf(x_79, x_86);
lean_dec(x_79);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_86);
lean_dec(x_36);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_77, 0, x_89);
return x_77;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_free_object(x_77);
x_90 = lean_box(0);
x_91 = l_Lean_Expr_const___override(x_86, x_90);
x_92 = l_Lean_Meta_mkEqRefl(x_91, x_5, x_6, x_7, x_8, x_80);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = lean_mk_string_unchecked("False", 5, 5);
x_96 = l_Lean_Name_mkStr1(x_95);
x_97 = l_Lean_Expr_const___override(x_96, x_90);
x_98 = lean_mk_string_unchecked("eq_false_of_decide", 18, 18);
x_99 = l_Lean_Name_mkStr1(x_98);
x_100 = l_Lean_Expr_const___override(x_99, x_90);
x_101 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_102 = lean_unsigned_to_nat(3u);
x_103 = lean_mk_empty_array_with_capacity(x_102);
x_104 = lean_array_push(x_103, x_1);
x_105 = lean_array_push(x_104, x_101);
x_106 = lean_array_push(x_105, x_94);
x_107 = l_Lean_mkAppN(x_100, x_106);
lean_dec(x_106);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_109, 0, x_97);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*2, x_31);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_92, 0, x_110);
return x_92;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_111 = lean_ctor_get(x_92, 0);
x_112 = lean_ctor_get(x_92, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_92);
x_113 = lean_mk_string_unchecked("False", 5, 5);
x_114 = l_Lean_Name_mkStr1(x_113);
x_115 = l_Lean_Expr_const___override(x_114, x_90);
x_116 = lean_mk_string_unchecked("eq_false_of_decide", 18, 18);
x_117 = l_Lean_Name_mkStr1(x_116);
x_118 = l_Lean_Expr_const___override(x_117, x_90);
x_119 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_120 = lean_unsigned_to_nat(3u);
x_121 = lean_mk_empty_array_with_capacity(x_120);
x_122 = lean_array_push(x_121, x_1);
x_123 = lean_array_push(x_122, x_119);
x_124 = lean_array_push(x_123, x_111);
x_125 = l_Lean_mkAppN(x_118, x_124);
lean_dec(x_124);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_127, 0, x_115);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set_uint8(x_127, sizeof(void*)*2, x_31);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_112);
return x_129;
}
}
else
{
uint8_t x_130; 
lean_dec(x_36);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_92);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_92, 0);
x_132 = lean_ctor_get(x_92, 1);
lean_inc(x_132);
lean_inc(x_131);
x_17 = x_92;
x_18 = x_131;
x_19 = x_132;
goto block_22;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_92, 0);
x_134 = lean_ctor_get(x_92, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_92);
lean_inc(x_134);
lean_inc(x_133);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_17 = x_135;
x_18 = x_133;
x_19 = x_134;
goto block_22;
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_81);
lean_free_object(x_77);
lean_dec(x_79);
x_136 = lean_box(0);
x_137 = l_Lean_Expr_const___override(x_83, x_136);
x_138 = l_Lean_Meta_mkEqRefl(x_137, x_5, x_6, x_7, x_8, x_80);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = lean_mk_string_unchecked("True", 4, 4);
x_142 = l_Lean_Name_mkStr1(x_141);
x_143 = l_Lean_Expr_const___override(x_142, x_136);
x_144 = lean_mk_string_unchecked("eq_true_of_decide", 17, 17);
x_145 = l_Lean_Name_mkStr1(x_144);
x_146 = l_Lean_Expr_const___override(x_145, x_136);
x_147 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_148 = lean_unsigned_to_nat(3u);
x_149 = lean_mk_empty_array_with_capacity(x_148);
x_150 = lean_array_push(x_149, x_1);
x_151 = lean_array_push(x_150, x_147);
x_152 = lean_array_push(x_151, x_140);
x_153 = l_Lean_mkAppN(x_146, x_152);
lean_dec(x_152);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_155, 0, x_143);
lean_ctor_set(x_155, 1, x_154);
lean_ctor_set_uint8(x_155, sizeof(void*)*2, x_31);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_138, 0, x_156);
return x_138;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_157 = lean_ctor_get(x_138, 0);
x_158 = lean_ctor_get(x_138, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_138);
x_159 = lean_mk_string_unchecked("True", 4, 4);
x_160 = l_Lean_Name_mkStr1(x_159);
x_161 = l_Lean_Expr_const___override(x_160, x_136);
x_162 = lean_mk_string_unchecked("eq_true_of_decide", 17, 17);
x_163 = l_Lean_Name_mkStr1(x_162);
x_164 = l_Lean_Expr_const___override(x_163, x_136);
x_165 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_166 = lean_unsigned_to_nat(3u);
x_167 = lean_mk_empty_array_with_capacity(x_166);
x_168 = lean_array_push(x_167, x_1);
x_169 = lean_array_push(x_168, x_165);
x_170 = lean_array_push(x_169, x_157);
x_171 = l_Lean_mkAppN(x_164, x_170);
lean_dec(x_170);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_171);
x_173 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_173, 0, x_161);
lean_ctor_set(x_173, 1, x_172);
lean_ctor_set_uint8(x_173, sizeof(void*)*2, x_31);
x_174 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_174, 0, x_173);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_158);
return x_175;
}
}
else
{
uint8_t x_176; 
lean_dec(x_36);
lean_dec(x_1);
x_176 = !lean_is_exclusive(x_138);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_138, 0);
x_178 = lean_ctor_get(x_138, 1);
lean_inc(x_178);
lean_inc(x_177);
x_17 = x_138;
x_18 = x_177;
x_19 = x_178;
goto block_22;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_138, 0);
x_180 = lean_ctor_get(x_138, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_138);
lean_inc(x_180);
lean_inc(x_179);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_17 = x_181;
x_18 = x_179;
x_19 = x_180;
goto block_22;
}
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_182 = lean_ctor_get(x_77, 0);
x_183 = lean_ctor_get(x_77, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_77);
x_184 = lean_mk_string_unchecked("Bool", 4, 4);
x_185 = lean_mk_string_unchecked("true", 4, 4);
lean_inc(x_184);
x_186 = l_Lean_Name_mkStr2(x_184, x_185);
x_187 = l_Lean_Expr_isConstOf(x_182, x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; 
lean_dec(x_186);
x_188 = lean_mk_string_unchecked("false", 5, 5);
x_189 = l_Lean_Name_mkStr2(x_184, x_188);
x_190 = l_Lean_Expr_isConstOf(x_182, x_189);
lean_dec(x_182);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_189);
lean_dec(x_36);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_191 = lean_box(0);
x_192 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_192, 0, x_191);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_183);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_box(0);
x_195 = l_Lean_Expr_const___override(x_189, x_194);
x_196 = l_Lean_Meta_mkEqRefl(x_195, x_5, x_6, x_7, x_8, x_183);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_199 = x_196;
} else {
 lean_dec_ref(x_196);
 x_199 = lean_box(0);
}
x_200 = lean_mk_string_unchecked("False", 5, 5);
x_201 = l_Lean_Name_mkStr1(x_200);
x_202 = l_Lean_Expr_const___override(x_201, x_194);
x_203 = lean_mk_string_unchecked("eq_false_of_decide", 18, 18);
x_204 = l_Lean_Name_mkStr1(x_203);
x_205 = l_Lean_Expr_const___override(x_204, x_194);
x_206 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_207 = lean_unsigned_to_nat(3u);
x_208 = lean_mk_empty_array_with_capacity(x_207);
x_209 = lean_array_push(x_208, x_1);
x_210 = lean_array_push(x_209, x_206);
x_211 = lean_array_push(x_210, x_197);
x_212 = l_Lean_mkAppN(x_205, x_211);
lean_dec(x_211);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_214 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_214, 0, x_202);
lean_ctor_set(x_214, 1, x_213);
lean_ctor_set_uint8(x_214, sizeof(void*)*2, x_31);
x_215 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_215, 0, x_214);
if (lean_is_scalar(x_199)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_199;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_198);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_36);
lean_dec(x_1);
x_217 = lean_ctor_get(x_196, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_196, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_219 = x_196;
} else {
 lean_dec_ref(x_196);
 x_219 = lean_box(0);
}
lean_inc(x_218);
lean_inc(x_217);
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_217);
lean_ctor_set(x_220, 1, x_218);
x_17 = x_220;
x_18 = x_217;
x_19 = x_218;
goto block_22;
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_184);
lean_dec(x_182);
x_221 = lean_box(0);
x_222 = l_Lean_Expr_const___override(x_186, x_221);
x_223 = l_Lean_Meta_mkEqRefl(x_222, x_5, x_6, x_7, x_8, x_183);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_226 = x_223;
} else {
 lean_dec_ref(x_223);
 x_226 = lean_box(0);
}
x_227 = lean_mk_string_unchecked("True", 4, 4);
x_228 = l_Lean_Name_mkStr1(x_227);
x_229 = l_Lean_Expr_const___override(x_228, x_221);
x_230 = lean_mk_string_unchecked("eq_true_of_decide", 17, 17);
x_231 = l_Lean_Name_mkStr1(x_230);
x_232 = l_Lean_Expr_const___override(x_231, x_221);
x_233 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_234 = lean_unsigned_to_nat(3u);
x_235 = lean_mk_empty_array_with_capacity(x_234);
x_236 = lean_array_push(x_235, x_1);
x_237 = lean_array_push(x_236, x_233);
x_238 = lean_array_push(x_237, x_224);
x_239 = l_Lean_mkAppN(x_232, x_238);
lean_dec(x_238);
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_239);
x_241 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_241, 0, x_229);
lean_ctor_set(x_241, 1, x_240);
lean_ctor_set_uint8(x_241, sizeof(void*)*2, x_31);
x_242 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_242, 0, x_241);
if (lean_is_scalar(x_226)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_226;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_225);
return x_243;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_36);
lean_dec(x_1);
x_244 = lean_ctor_get(x_223, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_223, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_246 = x_223;
} else {
 lean_dec_ref(x_223);
 x_246 = lean_box(0);
}
lean_inc(x_245);
lean_inc(x_244);
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_245);
x_17 = x_247;
x_18 = x_244;
x_19 = x_245;
goto block_22;
}
}
}
}
else
{
uint8_t x_248; 
lean_dec(x_36);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_248 = !lean_is_exclusive(x_77);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_77, 0);
x_250 = lean_ctor_get(x_77, 1);
lean_inc(x_250);
lean_inc(x_249);
x_17 = x_77;
x_18 = x_249;
x_19 = x_250;
goto block_22;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_77, 0);
x_252 = lean_ctor_get(x_77, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_77);
lean_inc(x_252);
lean_inc(x_251);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
x_17 = x_253;
x_18 = x_251;
x_19 = x_252;
goto block_22;
}
}
}
else
{
uint8_t x_254; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_254 = !lean_is_exclusive(x_35);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_35, 0);
x_256 = lean_ctor_get(x_35, 1);
lean_inc(x_256);
lean_inc(x_255);
x_17 = x_35;
x_18 = x_255;
x_19 = x_256;
goto block_22;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_35, 0);
x_258 = lean_ctor_get(x_35, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_35);
lean_inc(x_258);
lean_inc(x_257);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
x_17 = x_259;
x_18 = x_257;
x_19 = x_258;
goto block_22;
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
goto block_30;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
goto block_30;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
goto block_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preDefault___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_12 = l_Lean_Meta_Simp_userPreSimprocs(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preDefault___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Meta_Simp_simpMatch(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 2)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = lean_apply_9(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_Simp_mkEqTransResultStep(x_17, x_20, x_6, x_7, x_8, x_9, x_21);
return x_22;
}
else
{
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_19;
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_preDefault___lam__0___boxed), 9, 0);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_Meta_Simp_rewritePre(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 2)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_preDefault___lam__1___boxed), 11, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_19; 
x_19 = l_Lean_Meta_Simp_preDefault___lam__2(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_Meta_Simp_preDefault___lam__2(x_18, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Meta_Simp_mkEqTransResultStep(x_20, x_23, x_6, x_7, x_8, x_9, x_24);
return x_25;
}
else
{
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_22;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
else
{
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preDefault___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_preDefault___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preDefault___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_preDefault___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_2);
x_11 = l_Lean_Meta_Simp_simpArith___redArg(x_2, x_4, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 2)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = lean_apply_9(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_Simp_mkEqTransResultStep(x_17, x_20, x_6, x_7, x_8, x_9, x_21);
return x_22;
}
else
{
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_19;
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Meta_Simp_simpGround(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 2)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_14;
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_12 = l_Lean_Meta_Simp_userPostSimprocs(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_preDefault___lam__0___boxed), 9, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_postDefault___lam__1), 10, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_Meta_Simp_rewritePost(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 2)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_postDefault___lam__0), 10, 1);
lean_closure_set(x_19, 0, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; 
x_20 = l_Lean_Meta_Simp_postDefault___lam__2(x_1, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_23 = l_Lean_Meta_Simp_postDefault___lam__2(x_1, x_19, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_Simp_mkEqTransResultStep(x_21, x_24, x_6, x_7, x_8, x_9, x_25);
return x_26;
}
else
{
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_23;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_postDefault___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_postDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis_go(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_10; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_10 = l_Lean_Expr_isEq(x_2);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Expr_isHEq(x_2);
lean_dec(x_2);
x_4 = x_11;
goto block_9;
}
else
{
lean_dec(x_2);
x_4 = x_10;
goto block_9;
}
block_9:
{
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_expr_has_loose_bvar(x_3, x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_6;
}
else
{
x_1 = x_3;
goto _start;
}
}
else
{
x_1 = x_3;
goto _start;
}
}
}
else
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isFalse(x_1);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isEqnThmHypothesis_go___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Simp_isEqnThmHypothesis_go(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_isForall(x_1);
if (x_2 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = l_Lean_Meta_Simp_isEqnThmHypothesis_go(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isEqnThmHypothesis___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_5, x_12);
if (x_13 == 1)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_5, x_16);
lean_dec(x_5);
x_18 = lean_array_fget(x_4, x_17);
if (lean_obj_tag(x_18) == 0)
{
x_5 = x_17;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_29; lean_object* x_57; lean_object* x_58; uint8_t x_64; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_57 = lean_ctor_get(x_2, 8);
x_64 = l_Lean_LocalDecl_isImplementationDetail(x_20);
if (x_64 == 0)
{
if (x_3 == 0)
{
goto block_63;
}
else
{
if (x_64 == 0)
{
goto block_56;
}
else
{
goto block_63;
}
}
}
else
{
lean_dec(x_21);
lean_dec(x_20);
x_5 = x_17;
goto _start;
}
block_28:
{
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
x_5 = x_17;
x_11 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_25 = l_Lean_LocalDecl_toExpr(x_20);
if (lean_is_scalar(x_21)) {
 x_26 = lean_alloc_ctor(1, 1, 0);
} else {
 x_26 = x_21;
}
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
block_54:
{
lean_object* x_30; lean_object* x_31; uint64_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_30 = lean_ctor_get(x_6, 3);
x_31 = lean_ctor_get(x_30, 0);
x_32 = lean_ctor_get_uint64(x_30, sizeof(void*)*1);
x_33 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 8);
x_34 = lean_ctor_get(x_7, 1);
x_35 = lean_ctor_get(x_7, 2);
x_36 = lean_ctor_get(x_7, 3);
x_37 = lean_ctor_get(x_7, 4);
x_38 = lean_ctor_get(x_7, 5);
x_39 = lean_ctor_get(x_7, 6);
x_40 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 9);
x_41 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 10);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_31);
x_42 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 2, x_35);
lean_ctor_set(x_42, 3, x_36);
lean_ctor_set(x_42, 4, x_37);
lean_ctor_set(x_42, 5, x_38);
lean_ctor_set(x_42, 6, x_39);
lean_ctor_set_uint64(x_42, sizeof(void*)*7, x_32);
lean_ctor_set_uint8(x_42, sizeof(void*)*7 + 8, x_33);
lean_ctor_set_uint8(x_42, sizeof(void*)*7 + 9, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*7 + 10, x_41);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_43 = l_Lean_Meta_isExprDefEq(x_1, x_29, x_42, x_8, x_9, x_10, x_11);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_unbox(x_44);
lean_dec(x_44);
x_22 = x_46;
x_23 = x_45;
goto block_28;
}
else
{
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_dec(x_43);
x_49 = lean_unbox(x_47);
lean_dec(x_47);
x_22 = x_49;
x_23 = x_48;
goto block_28;
}
else
{
uint8_t x_50; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
return x_43;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_43, 0);
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_43);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
block_56:
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_20, 3);
lean_inc(x_55);
x_29 = x_55;
goto block_54;
}
block_61:
{
uint8_t x_59; 
x_59 = lean_nat_dec_le(x_57, x_58);
lean_dec(x_58);
if (x_59 == 0)
{
goto block_56;
}
else
{
lean_dec(x_21);
lean_dec(x_20);
x_5 = x_17;
goto _start;
}
}
block_63:
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_20, 0);
lean_inc(x_62);
x_58 = x_62;
goto block_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_5, x_14);
if (x_15 == 1)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_5, x_18);
lean_dec(x_5);
x_20 = lean_array_fget(x_4, x_19);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_21 = l_Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_5 = x_19;
x_13 = x_23;
goto _start;
}
else
{
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
return x_21;
}
}
else
{
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_array_get_size(x_13);
x_15 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_3, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_array_get_size(x_16);
x_18 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_16, x_17, x_6, x_8, x_9, x_10, x_11, x_12);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_array_get_size(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_15 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_13, x_14, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_4, 0);
x_19 = l_Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
return x_19;
}
else
{
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_4, 1);
x_14 = l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_Meta_Simp_getConfig___redArg(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
lean_dec(x_11);
x_14 = lean_ctor_get(x_5, 2);
x_15 = l_Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0(x_1, x_3, x_13, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__0(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__1_spec__1(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0_spec__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0_spec__0(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f_spec__0(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_4);
lean_inc(x_1);
x_9 = l_Lean_FVarId_getDecl___redArg(x_1, x_4, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_31; lean_object* x_36; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_36 = lean_ctor_get(x_10, 3);
lean_inc(x_36);
x_31 = x_36;
goto block_35;
block_30:
{
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_1);
x_13 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f(x_2, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box(0);
x_15 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Meta_unifyEq_x3f(x_2, x_1, x_14, x_3, x_15, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f(x_24, x_4, x_5, x_6, x_7, x_23);
lean_dec(x_4);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
block_35:
{
uint8_t x_32; 
x_32 = l_Lean_Expr_isEq(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_10, 3);
lean_inc(x_33);
lean_dec(x_10);
x_34 = l_Lean_Expr_isHEq(x_33);
lean_dec(x_33);
x_12 = x_34;
goto block_30;
}
else
{
lean_dec(x_10);
x_12 = x_32;
goto block_30;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_9);
if (x_37 == 0)
{
return x_9;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_9, 0);
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_9);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_14; lean_object* x_15; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_21 = l_Lean_Meta_intro1Core(x_1, x_20, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lam__0___boxed), 7, 0);
lean_inc(x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lam__1), 8, 3);
lean_closure_set(x_27, 0, x_24);
lean_closure_set(x_27, 1, x_25);
lean_closure_set(x_27, 2, x_26);
x_28 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_25, x_27, x_2, x_3, x_4, x_5, x_23);
if (lean_obj_tag(x_28) == 0)
{
lean_dec(x_1);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_14 = x_29;
x_15 = x_30;
goto block_18;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = lean_ctor_get(x_21, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_14 = x_31;
x_15 = x_32;
goto block_18;
}
block_13:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___lam__0___boxed), 5, 0);
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_8 = lean_mk_string_unchecked("Lean.Meta.Tactic.Simp.Rewrite", 29, 29);
x_9 = lean_mk_string_unchecked("Lean.Meta.Simp.dischargeEqnThmHypothesis\?", 41, 41);
x_10 = lean_unsigned_to_nat(580u);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_mk_string_unchecked("assertion violation: isEqnThmHypothesis e\n  ", 44, 44);
x_13 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_14 = l_panic___at___Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_spec__0(x_13, x_2, x_3, x_4, x_5, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_15 = lean_box(0);
lean_inc(x_2);
x_16 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_15, x_2, x_3, x_4, x_5, x_6);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_canUnfoldAtMatcher___boxed), 5, 0);
x_20 = l_Lean_Expr_mvarId_x21(x_17);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 4);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 5);
lean_inc(x_28);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_19);
x_30 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_31 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
lean_dec(x_2);
x_32 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_25);
lean_ctor_set(x_32, 3, x_26);
lean_ctor_set(x_32, 4, x_27);
lean_ctor_set(x_32, 5, x_28);
lean_ctor_set(x_32, 6, x_29);
lean_ctor_set_uint64(x_32, sizeof(void*)*7, x_22);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 8, x_23);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 9, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 10, x_31);
lean_inc(x_3);
x_33 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f(x_20, x_32, x_3, x_4, x_5, x_18);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_17, x_3, x_35);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_34);
lean_dec(x_17);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_33);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_33, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set(x_33, 0, x_46);
return x_33;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
lean_dec(x_33);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_17);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_33);
if (x_50 == 0)
{
return x_33;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_33, 0);
x_52 = lean_ctor_get(x_33, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_33);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_Simp_dischargeRfl_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_10(x_1, x_5, x_6, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_Simp_dischargeRfl_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___Lean_Meta_Simp_dischargeRfl_spec__0___redArg___lam__0), 11, 4);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_4);
lean_closure_set(x_12, 2, x_5);
lean_closure_set(x_12, 3, x_6);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = lean_unbox(x_13);
x_16 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___redArg(x_15, x_14, x_1, x_12, x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_Simp_dischargeRfl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_forallTelescope___at___Lean_Meta_Simp_dischargeRfl_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeRfl___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_mk_string_unchecked("Eq", 2, 2);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Expr_isAppOfArity(x_2, x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_58; uint8_t x_59; lean_object* x_60; lean_object* x_94; uint8_t x_95; lean_object* x_123; uint8_t x_124; 
x_17 = l_Lean_Expr_appFn_x21(x_2);
x_18 = l_Lean_Expr_appFn_x21(x_17);
x_19 = l_Lean_Expr_appArg_x21(x_18);
lean_dec(x_18);
x_20 = l_Lean_Expr_appArg_x21(x_17);
lean_dec(x_17);
x_94 = l_Lean_Expr_appArg_x21(x_2);
x_123 = l_Lean_Expr_getAppFn(x_20);
x_124 = l_Lean_Expr_isMVar(x_123);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; uint8_t x_126; 
x_125 = l_Lean_Expr_getAppFn(x_94);
x_126 = l_Lean_Expr_isMVar(x_125);
lean_dec(x_125);
x_95 = x_126;
goto block_122;
}
else
{
x_95 = x_124;
goto block_122;
}
block_57:
{
lean_object* x_27; 
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_19);
x_27 = l_Lean_Meta_getLevel(x_19, x_22, x_23, x_24, x_25, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_mk_string_unchecked("rfl", 3, 3);
x_31 = l_Lean_Name_mkStr1(x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Expr_const___override(x_31, x_33);
x_35 = l_Lean_mkAppB(x_34, x_19, x_20);
x_36 = lean_box(0);
x_37 = lean_box(1);
x_38 = lean_unbox(x_36);
x_39 = lean_unbox(x_36);
x_40 = lean_unbox(x_37);
x_41 = l_Lean_Meta_mkLambdaFVars(x_1, x_35, x_38, x_21, x_39, x_40, x_22, x_23, x_24, x_25, x_29);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_41);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_41);
if (x_49 == 0)
{
return x_41;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_41, 0);
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_41);
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
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
x_53 = !lean_is_exclusive(x_27);
if (x_53 == 0)
{
return x_27;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_27, 0);
x_55 = lean_ctor_get(x_27, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_27);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
block_93:
{
if (x_59 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_63 = lean_mk_string_unchecked("Meta", 4, 4);
x_64 = lean_mk_string_unchecked("Tactic", 6, 6);
x_65 = lean_mk_string_unchecked("simp", 4, 4);
x_66 = lean_mk_string_unchecked("discharge", 9, 9);
x_67 = l_Lean_Name_mkStr4(x_63, x_64, x_65, x_66);
lean_inc(x_67);
x_68 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_67, x_8, x_60);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_67);
lean_dec(x_2);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_21 = x_58;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
x_26 = x_71;
goto block_57;
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_68);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_73 = lean_ctor_get(x_68, 1);
x_74 = lean_ctor_get(x_68, 0);
lean_dec(x_74);
x_75 = lean_mk_string_unchecked("Discharging with rfl: ", 22, 22);
x_76 = l_Lean_stringToMessageData(x_75);
lean_dec(x_75);
x_77 = l_Lean_MessageData_ofExpr(x_2);
lean_ctor_set_tag(x_68, 7);
lean_ctor_set(x_68, 1, x_77);
lean_ctor_set(x_68, 0, x_76);
x_78 = lean_mk_string_unchecked("", 0, 0);
x_79 = l_Lean_stringToMessageData(x_78);
lean_dec(x_78);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_68);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_67, x_80, x_6, x_7, x_8, x_9, x_73);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_21 = x_58;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
x_26 = x_82;
goto block_57;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_83 = lean_ctor_get(x_68, 1);
lean_inc(x_83);
lean_dec(x_68);
x_84 = lean_mk_string_unchecked("Discharging with rfl: ", 22, 22);
x_85 = l_Lean_stringToMessageData(x_84);
lean_dec(x_84);
x_86 = l_Lean_MessageData_ofExpr(x_2);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_mk_string_unchecked("", 0, 0);
x_89 = l_Lean_stringToMessageData(x_88);
lean_dec(x_88);
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_67, x_90, x_6, x_7, x_8, x_9, x_83);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_21 = x_58;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
x_26 = x_92;
goto block_57;
}
}
}
}
block_122:
{
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_94);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_10);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; uint64_t x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; 
x_98 = lean_ctor_get(x_4, 3);
x_99 = lean_ctor_get(x_98, 0);
x_100 = lean_ctor_get_uint64(x_98, sizeof(void*)*1);
x_101 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_102 = lean_ctor_get(x_6, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_6, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_6, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_6, 4);
lean_inc(x_105);
x_106 = lean_ctor_get(x_6, 5);
lean_inc(x_106);
x_107 = lean_ctor_get(x_6, 6);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_109 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
lean_inc(x_99);
x_110 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_110, 0, x_99);
lean_ctor_set(x_110, 1, x_102);
lean_ctor_set(x_110, 2, x_103);
lean_ctor_set(x_110, 3, x_104);
lean_ctor_set(x_110, 4, x_105);
lean_ctor_set(x_110, 5, x_106);
lean_ctor_set(x_110, 6, x_107);
lean_ctor_set_uint64(x_110, sizeof(void*)*7, x_100);
lean_ctor_set_uint8(x_110, sizeof(void*)*7 + 8, x_101);
lean_ctor_set_uint8(x_110, sizeof(void*)*7 + 9, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*7 + 10, x_109);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_20);
x_111 = l_Lean_Meta_isExprDefEq(x_20, x_94, x_110, x_7, x_8, x_9, x_10);
lean_dec(x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_unbox(x_112);
lean_dec(x_112);
x_58 = x_95;
x_59 = x_114;
x_60 = x_113;
goto block_93;
}
else
{
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
lean_dec(x_111);
x_117 = lean_unbox(x_115);
lean_dec(x_115);
x_58 = x_95;
x_59 = x_117;
x_60 = x_116;
goto block_93;
}
else
{
uint8_t x_118; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_118 = !lean_is_exclusive(x_111);
if (x_118 == 0)
{
return x_111;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_111, 0);
x_120 = lean_ctor_get(x_111, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_111);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeRfl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_dischargeRfl___lam__0___boxed), 10, 0);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_Meta_forallTelescope___at___Lean_Meta_Simp_dischargeRfl_spec__0___redArg(x_1, x_10, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_Simp_dischargeRfl_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Meta_forallTelescope___at___Lean_Meta_Simp_dischargeRfl_spec__0___redArg(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_Simp_dischargeRfl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lean_Meta_forallTelescope___at___Lean_Meta_Simp_dischargeRfl_spec__0(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeRfl___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_dischargeRfl___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_119; 
x_10 = l_Lean_Expr_cleanupAnnotations(x_1);
lean_inc(x_10);
x_119 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_10);
if (x_119 == 0)
{
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
goto block_118;
}
else
{
lean_object* x_120; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_10);
x_120 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_dischargeUsingAssumption_x3f(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_10);
x_123 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f(x_10, x_5, x_6, x_7, x_8, x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_125;
goto block_118;
}
else
{
lean_dec(x_124);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_123;
}
}
else
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_123;
}
}
else
{
lean_dec(x_121);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_120;
}
}
else
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_120;
}
}
block_118:
{
lean_object* x_19; 
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_19 = lean_simp(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_22);
x_23 = l_Lean_Meta_Simp_dischargeRfl(x_22, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
lean_dec(x_10);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
x_26 = l_Lean_Expr_isTrue(x_22);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
return x_23;
}
else
{
lean_object* x_27; 
lean_dec(x_23);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_27 = l_Lean_Meta_Simp_Result_getProof(x_20, x_14, x_15, x_16, x_17, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_mkOfEqTrue(x_28, x_14, x_15, x_16, x_17, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
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
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_34);
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
else
{
uint8_t x_42; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_42 = !lean_is_exclusive(x_27);
if (x_42 == 0)
{
return x_27;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_27, 0);
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_27);
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
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_23, 1);
x_48 = lean_ctor_get(x_23, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_24);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_24, 0);
x_51 = l_Lean_Meta_Simp_Result_getProof(x_20, x_14, x_15, x_16, x_17, x_47);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_mk_string_unchecked("Eq", 2, 2);
x_55 = lean_mk_string_unchecked("mpr", 3, 3);
x_56 = l_Lean_Name_mkStr2(x_54, x_55);
x_57 = lean_box(0);
x_58 = lean_box(0);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_58);
lean_ctor_set(x_23, 0, x_57);
x_59 = l_Lean_Expr_const___override(x_56, x_23);
x_60 = l_Lean_mkApp4(x_59, x_10, x_22, x_53, x_50);
lean_ctor_set(x_24, 0, x_60);
lean_ctor_set(x_51, 0, x_24);
return x_51;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_61 = lean_ctor_get(x_51, 0);
x_62 = lean_ctor_get(x_51, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_51);
x_63 = lean_mk_string_unchecked("Eq", 2, 2);
x_64 = lean_mk_string_unchecked("mpr", 3, 3);
x_65 = l_Lean_Name_mkStr2(x_63, x_64);
x_66 = lean_box(0);
x_67 = lean_box(0);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_67);
lean_ctor_set(x_23, 0, x_66);
x_68 = l_Lean_Expr_const___override(x_65, x_23);
x_69 = l_Lean_mkApp4(x_68, x_10, x_22, x_61, x_50);
lean_ctor_set(x_24, 0, x_69);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_24);
lean_ctor_set(x_70, 1, x_62);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_free_object(x_24);
lean_dec(x_50);
lean_free_object(x_23);
lean_dec(x_22);
lean_dec(x_10);
x_71 = !lean_is_exclusive(x_51);
if (x_71 == 0)
{
return x_51;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_51, 0);
x_73 = lean_ctor_get(x_51, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_51);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_24, 0);
lean_inc(x_75);
lean_dec(x_24);
x_76 = l_Lean_Meta_Simp_Result_getProof(x_20, x_14, x_15, x_16, x_17, x_47);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = lean_mk_string_unchecked("Eq", 2, 2);
x_81 = lean_mk_string_unchecked("mpr", 3, 3);
x_82 = l_Lean_Name_mkStr2(x_80, x_81);
x_83 = lean_box(0);
x_84 = lean_box(0);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_84);
lean_ctor_set(x_23, 0, x_83);
x_85 = l_Lean_Expr_const___override(x_82, x_23);
x_86 = l_Lean_mkApp4(x_85, x_10, x_22, x_77, x_75);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
if (lean_is_scalar(x_79)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_79;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_78);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_75);
lean_free_object(x_23);
lean_dec(x_22);
lean_dec(x_10);
x_89 = lean_ctor_get(x_76, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_76, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_91 = x_76;
} else {
 lean_dec_ref(x_76);
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
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_23, 1);
lean_inc(x_93);
lean_dec(x_23);
x_94 = lean_ctor_get(x_24, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_95 = x_24;
} else {
 lean_dec_ref(x_24);
 x_95 = lean_box(0);
}
x_96 = l_Lean_Meta_Simp_Result_getProof(x_20, x_14, x_15, x_16, x_17, x_93);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_99 = x_96;
} else {
 lean_dec_ref(x_96);
 x_99 = lean_box(0);
}
x_100 = lean_mk_string_unchecked("Eq", 2, 2);
x_101 = lean_mk_string_unchecked("mpr", 3, 3);
x_102 = l_Lean_Name_mkStr2(x_100, x_101);
x_103 = lean_box(0);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_Expr_const___override(x_102, x_105);
x_107 = l_Lean_mkApp4(x_106, x_10, x_22, x_97, x_94);
if (lean_is_scalar(x_95)) {
 x_108 = lean_alloc_ctor(1, 1, 0);
} else {
 x_108 = x_95;
}
lean_ctor_set(x_108, 0, x_107);
if (lean_is_scalar(x_99)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_99;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_98);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_22);
lean_dec(x_10);
x_110 = lean_ctor_get(x_96, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_96, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_112 = x_96;
} else {
 lean_dec_ref(x_96);
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
}
}
else
{
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
return x_23;
}
}
else
{
uint8_t x_114; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_114 = !lean_is_exclusive(x_19);
if (x_114 == 0)
{
return x_19;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_19, 0);
x_116 = lean_ctor_get(x_19, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_19);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkMethods(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_preDefault), 10, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_postDefault___boxed), 10, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_dpreDefault___boxed), 10, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_dpostDefault___boxed), 10, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set(x_8, 3, x_7);
lean_ctor_set(x_8, 4, x_2);
lean_ctor_set_uint8(x_8, sizeof(void*)*5, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkMethods___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Meta_Simp_mkMethods(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDefaultMethodsCore(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_dischargeDefault_x3f), 9, 0);
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Meta_Simp_mkMethods(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDefaultMethods(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_Lean_Meta_Simp_simprocs;
x_6 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Array_empty(lean_box(0));
x_8 = l_Lean_Meta_Simp_mkDefaultMethodsCore(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Meta_Simp_getSimprocs(x_1, x_2, x_3);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_mk_empty_array_with_capacity(x_13);
x_15 = lean_array_push(x_14, x_12);
x_16 = l_Lean_Meta_Simp_mkDefaultMethodsCore(x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_mk_empty_array_with_capacity(x_19);
x_21 = lean_array_push(x_20, x_17);
x_22 = l_Lean_Meta_Simp_mkDefaultMethodsCore(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDefaultMethods___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_mkDefaultMethods(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Lean_Meta_ACLt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatchEqsExt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_UnifyEq(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_BinderNameHint(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_ACLt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatchEqsExt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_UnifyEq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_BinderNameHint(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
