// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.BVDecide
// Imports: Std.Sat.AIG.CNF Std.Sat.AIG.RelabelNat Std.Tactic.BVDecide.Bitblast Std.Tactic.BVDecide.Syntax Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.SatAtBVLogical Lean.Elab.Tactic.BVDecide.Frontend.Normalize Lean.Elab.Tactic.BVDecide.Frontend.LRAT
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_uninterpretedExplainer(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_reflectBV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2___redArg(lean_object*);
extern lean_object* l_Lean_instBEqFVarId;
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
uint32_t lean_int32_of_nat(lean_object*);
uint8_t lean_int16_dec_le(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_unusedHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_forInStep_go___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__13___boxed(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at___Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer_spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_remove_file(lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__2___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addDerivedEquation___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
double lean_float_div(double, double);
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint16_t lean_uint16_of_nat_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addUninterpretedSymbol___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int64_to_int_sint(uint64_t);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addUnusedRelevantHypothesis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at___Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__15(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
extern uint8_t l_instInhabitedBool;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_toString(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__8(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__14(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t lean_float_decLt(double, double);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_unusedHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Elab_Tactic_BVDecide_Frontend_explainCounterExampleQuality_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__7___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__7(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addUnusedRelevantHypothesis___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_MVarId_getNondepPropHyps_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_lazyPure___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addDerivedEquation___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_uninterpretedExplainer___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_equations___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_instInhabitedNat;
uint64_t lean_uint64_of_nat_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addUninterpretedSymbol(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21_spec__21(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2___redArg___boxed(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_explainers;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_equations___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addDerivedEquation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*);
lean_object* lean_int8_to_int(uint8_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at___Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at___Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addUninterpretedSymbol___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToExprInt32_mkNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__9(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvDecide___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0(lean_object*, lean_object*);
lean_object* l_BitVec_toNat(lean_object*, lean_object*);
lean_object* l_Lean_ShareCommon_shareCommon(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_explainCounterExampleQuality_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__10(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_forInStep_go___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int32_to_int(uint32_t);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_explainCounterExampleQuality_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_async;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_relabelNat_x27___at___Std_Sat_AIG_relabelNat___at___Std_Sat_AIG_Entrypoint_relabelNat___at___Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__0(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_uninterpretedExplainer_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_filter_go___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvDecide___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_unusedHyps___redArg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int64_dec_le(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_forInStep_go___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int32_dec_le(uint32_t, uint32_t);
uint16_t lean_int16_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_reflectBV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__12(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instHashableFVarId;
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_create_tempfile(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addUnusedRelevantHypothesis___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat_mk(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_explainCounterExampleQuality_spec__1(lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lean_diagnostics;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addUnusedRelevantHypothesis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_toCNF(lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_instToExprInt64_mkNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof_mkAuxDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_equations(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__6___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_length___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addUninterpretedSymbol___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__2___lam__0(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_equations___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int16_to_int(uint16_t);
lean_object* l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_reflectBV___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_unusedHyps___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_explainCounterExampleQuality(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instHashable;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int8_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_explainCounterExampleQuality_spec__2(lean_object*, size_t, size_t, lean_object*);
uint64_t lean_int64_of_nat(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__9(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t lean_int8_dec_le(uint8_t, uint8_t);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_filter_go___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addDerivedEquation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_GetElem_0__List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_explainCounterExampleQuality___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_MVarId_getNondepPropHyps_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint8_of_nat_mk(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer_spec__1(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg___lam__1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvDecide_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_uninterpretedExplainer_spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToExprInt8_mkNat(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_uninterpretedExplainer_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg___lam__0(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_run___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_instToExprInt16_mkNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__6(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_uninterpretedExplainer_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_forInStep_go___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Tactic_BVDecide_Gate_toString(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle(uint8_t);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide__1(lean_object*);
double lean_float_sub(double, double);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_3 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_4 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_5 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 2, x_5);
lean_ctor_set(x_10, 3, x_6);
lean_ctor_set(x_10, 4, x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
x_12 = l_instInhabitedNat;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_instInhabitedOfMonad___redArg(x_11, x_14);
x_16 = lean_panic_fn(x_15, x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_nat_dec_eq(x_4, x_1);
if (x_7 == 0)
{
x_3 = x_6;
goto _start;
}
else
{
lean_inc(x_5);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at___Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = l_Lean_RBNode_revFold___at___Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2_spec__2___redArg(x_1, x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_1 = x_9;
x_2 = x_3;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at___Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_revFold___at___Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_RBNode_revFold___at___Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2_spec__2___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_5 = x_1;
} else {
 lean_dec_ref(x_1);
 x_5 = lean_box(0);
}
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_nat_dec_eq(x_13, x_15);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_2);
x_17 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.BVDecide", 43, 43);
x_18 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.reconstructCounterExample", 60, 60);
x_19 = lean_unsigned_to_nat(73u);
x_20 = lean_unsigned_to_nat(6u);
x_21 = lean_mk_string_unchecked("assertion violation: bitIdx == currentBit\n      ", 48, 48);
x_22 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_17, x_18, x_19, x_20, x_21);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
x_23 = l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__0(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_dec(x_4);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_1 = x_4;
x_2 = x_25;
goto _start;
}
}
else
{
uint8_t x_27; 
x_27 = lean_unbox(x_14);
lean_dec(x_14);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
lean_dec(x_2);
x_6 = x_15;
x_7 = x_28;
goto block_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
lean_dec(x_2);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_shiftl(x_30, x_15);
x_32 = lean_nat_lor(x_29, x_31);
lean_dec(x_31);
lean_dec(x_29);
x_6 = x_15;
x_7 = x_32;
goto block_12;
}
}
block_12:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
if (lean_is_scalar(x_5)) {
 x_10 = lean_alloc_ctor(0, 2, 0);
} else {
 x_10 = x_5;
 lean_ctor_set_tag(x_10, 0);
}
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
x_1 = x_4;
x_2 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4_spec__4___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_6 = x_2;
} else {
 lean_dec_ref(x_2);
 x_6 = lean_box(0);
}
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_nat_dec_eq(x_14, x_16);
lean_dec(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_3);
x_18 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.BVDecide", 43, 43);
x_19 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.reconstructCounterExample", 60, 60);
x_20 = lean_unsigned_to_nat(73u);
x_21 = lean_unsigned_to_nat(6u);
x_22 = lean_mk_string_unchecked("assertion violation: bitIdx == currentBit\n      ", 48, 48);
x_23 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_18, x_19, x_20, x_21, x_22);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
x_24 = l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__0(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec(x_5);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4_spec__4___redArg(x_5, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = lean_unbox(x_15);
lean_dec(x_15);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
lean_dec(x_3);
x_7 = x_16;
x_8 = x_29;
goto block_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
lean_dec(x_3);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_shiftl(x_31, x_16);
x_33 = lean_nat_lor(x_30, x_32);
lean_dec(x_32);
lean_dec(x_30);
x_7 = x_16;
x_8 = x_33;
goto block_13;
}
}
block_13:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_7, x_9);
lean_dec(x_7);
if (lean_is_scalar(x_6)) {
 x_11 = lean_alloc_ctor(0, 2, 0);
} else {
 x_11 = x_6;
 lean_ctor_set_tag(x_11, 0);
}
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
x_12 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4_spec__4___redArg(x_5, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Std.Data.DHashMap.Internal.AssocList.Basic", 42, 42);
x_5 = lean_mk_string_unchecked("Std.DHashMap.Internal.AssocList.get!", 36, 36);
x_6 = lean_unsigned_to_nat(138u);
x_7 = lean_unsigned_to_nat(11u);
x_8 = lean_mk_string_unchecked("key is not present in hash table", 32, 32);
x_9 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_panic_fn(x_1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
x_14 = lean_nat_dec_eq(x_11, x_2);
if (x_14 == 0)
{
x_3 = x_13;
goto _start;
}
else
{
lean_dec(x_1);
lean_inc(x_12);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_5, x_4);
if (x_13 == 0)
{
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_14 = lean_array_uget(x_3, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_103 = lean_nat_add(x_16, x_1);
lean_dec(x_16);
x_104 = lean_array_get_size(x_2);
x_105 = lean_nat_dec_lt(x_103, x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_dec(x_103);
x_17 = x_13;
goto block_102;
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = lean_array_fget(x_2, x_103);
lean_dec(x_103);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
x_17 = x_108;
goto block_102;
}
block_102:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; lean_object* x_35; size_t x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
x_22 = lean_box(0);
x_23 = lean_array_get_size(x_20);
x_24 = lean_uint64_of_nat(x_21);
x_25 = lean_unsigned_to_nat(32u);
x_26 = lean_uint64_of_nat(x_25);
x_27 = lean_uint64_shift_right(x_24, x_26);
x_28 = lean_uint64_xor(x_24, x_27);
x_29 = lean_unsigned_to_nat(16u);
x_30 = lean_uint64_of_nat(x_29);
x_31 = lean_uint64_shift_right(x_28, x_30);
x_32 = lean_uint64_xor(x_28, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_usize_of_nat(x_35);
x_37 = lean_usize_sub(x_34, x_36);
x_38 = lean_usize_land(x_33, x_37);
x_39 = lean_array_uget(x_20, x_38);
x_40 = lean_ctor_get(x_15, 2);
lean_inc(x_40);
lean_dec(x_15);
x_41 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__1___redArg(x_21, x_22, x_39);
x_42 = lean_box(x_17);
x_43 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_41, x_40, x_42);
x_44 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0___redArg(x_21, x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_45 = lean_nat_add(x_19, x_35);
lean_dec(x_19);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_21);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_39);
x_47 = lean_array_uset(x_20, x_38, x_46);
x_48 = lean_unsigned_to_nat(2u);
x_49 = lean_nat_shiftl(x_45, x_48);
x_50 = lean_unsigned_to_nat(3u);
x_51 = lean_nat_div(x_49, x_50);
lean_dec(x_49);
x_52 = lean_array_get_size(x_47);
x_53 = lean_nat_dec_le(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__1___redArg(x_47);
lean_ctor_set(x_6, 1, x_54);
lean_ctor_set(x_6, 0, x_45);
x_7 = x_6;
goto block_12;
}
else
{
lean_ctor_set(x_6, 1, x_47);
lean_ctor_set(x_6, 0, x_45);
x_7 = x_6;
goto block_12;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_box(0);
x_56 = lean_array_uset(x_20, x_38, x_55);
x_57 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__4(lean_box(0), x_21, x_43, x_39);
x_58 = lean_array_uset(x_56, x_38, x_57);
lean_ctor_set(x_6, 1, x_58);
x_7 = x_6;
goto block_12;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint64_t x_64; lean_object* x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; lean_object* x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; size_t x_73; size_t x_74; lean_object* x_75; size_t x_76; size_t x_77; size_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_59 = lean_ctor_get(x_6, 0);
x_60 = lean_ctor_get(x_6, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_6);
x_61 = lean_ctor_get(x_15, 0);
lean_inc(x_61);
x_62 = lean_box(0);
x_63 = lean_array_get_size(x_60);
x_64 = lean_uint64_of_nat(x_61);
x_65 = lean_unsigned_to_nat(32u);
x_66 = lean_uint64_of_nat(x_65);
x_67 = lean_uint64_shift_right(x_64, x_66);
x_68 = lean_uint64_xor(x_64, x_67);
x_69 = lean_unsigned_to_nat(16u);
x_70 = lean_uint64_of_nat(x_69);
x_71 = lean_uint64_shift_right(x_68, x_70);
x_72 = lean_uint64_xor(x_68, x_71);
x_73 = lean_uint64_to_usize(x_72);
x_74 = lean_usize_of_nat(x_63);
lean_dec(x_63);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_usize_of_nat(x_75);
x_77 = lean_usize_sub(x_74, x_76);
x_78 = lean_usize_land(x_73, x_77);
x_79 = lean_array_uget(x_60, x_78);
x_80 = lean_ctor_get(x_15, 2);
lean_inc(x_80);
lean_dec(x_15);
x_81 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__1___redArg(x_61, x_62, x_79);
x_82 = lean_box(x_17);
x_83 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_81, x_80, x_82);
x_84 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0___redArg(x_61, x_79);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_85 = lean_nat_add(x_59, x_75);
lean_dec(x_59);
x_86 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_86, 0, x_61);
lean_ctor_set(x_86, 1, x_83);
lean_ctor_set(x_86, 2, x_79);
x_87 = lean_array_uset(x_60, x_78, x_86);
x_88 = lean_unsigned_to_nat(2u);
x_89 = lean_nat_shiftl(x_85, x_88);
x_90 = lean_unsigned_to_nat(3u);
x_91 = lean_nat_div(x_89, x_90);
lean_dec(x_89);
x_92 = lean_array_get_size(x_87);
x_93 = lean_nat_dec_le(x_91, x_92);
lean_dec(x_92);
lean_dec(x_91);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__1___redArg(x_87);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_85);
lean_ctor_set(x_95, 1, x_94);
x_7 = x_95;
goto block_12;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_85);
lean_ctor_set(x_96, 1, x_87);
x_7 = x_96;
goto block_12;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_box(0);
x_98 = lean_array_uset(x_60, x_78, x_97);
x_99 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__4(lean_box(0), x_61, x_83, x_79);
x_100 = lean_array_uset(x_98, x_78, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_59);
lean_ctor_set(x_101, 1, x_100);
x_7 = x_101;
goto block_12;
}
}
}
}
block_12:
{
lean_object* x_8; size_t x_9; size_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_5, x_9);
x_5 = x_10;
x_6 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_6 = l_Lean_instInhabitedExpr;
x_7 = l_instInhabitedBool;
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
return x_5;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_uget(x_2, x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2___redArg(x_12);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_13);
lean_inc(x_14);
x_16 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4___redArg(x_14, x_14, x_15);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; lean_object* x_35; size_t x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_1, 1);
x_21 = l_instInhabitedNat;
x_22 = lean_box(x_7);
lean_ctor_set(x_9, 1, x_22);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set(x_16, 0, x_21);
x_23 = lean_array_get_size(x_20);
x_24 = lean_uint64_of_nat(x_11);
x_25 = lean_unsigned_to_nat(32u);
x_26 = lean_uint64_of_nat(x_25);
x_27 = lean_uint64_shift_right(x_24, x_26);
x_28 = lean_uint64_xor(x_24, x_27);
x_29 = lean_unsigned_to_nat(16u);
x_30 = lean_uint64_of_nat(x_29);
x_31 = lean_uint64_shift_right(x_28, x_30);
x_32 = lean_uint64_xor(x_28, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_usize_of_nat(x_35);
x_37 = lean_usize_sub(x_34, x_36);
x_38 = lean_usize_land(x_33, x_37);
x_39 = lean_array_uget(x_20, x_38);
x_40 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__6___redArg(x_16, x_11, x_39);
lean_dec(x_39);
lean_dec(x_11);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_40, 1);
x_43 = lean_ctor_get(x_40, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; 
x_45 = lean_ctor_get(x_42, 1);
lean_dec(x_45);
x_46 = l_BitVec_ofNat(x_18, x_19);
lean_dec(x_19);
lean_ctor_set(x_40, 1, x_46);
lean_ctor_set(x_40, 0, x_18);
lean_ctor_set(x_42, 1, x_40);
x_47 = lean_array_push(x_5, x_42);
x_48 = lean_usize_add(x_4, x_36);
x_4 = x_48;
x_5 = x_47;
goto _start;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; 
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
lean_dec(x_42);
x_51 = l_BitVec_ofNat(x_18, x_19);
lean_dec(x_19);
lean_ctor_set(x_40, 1, x_51);
lean_ctor_set(x_40, 0, x_18);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_40);
x_53 = lean_array_push(x_5, x_52);
x_54 = lean_usize_add(x_4, x_36);
x_4 = x_54;
x_5 = x_53;
goto _start;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; size_t x_63; 
x_56 = lean_ctor_get(x_40, 1);
lean_inc(x_56);
lean_dec(x_40);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
x_59 = l_BitVec_ofNat(x_18, x_19);
lean_dec(x_19);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_18);
lean_ctor_set(x_60, 1, x_59);
if (lean_is_scalar(x_58)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_58;
}
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_array_push(x_5, x_61);
x_63 = lean_usize_add(x_4, x_36);
x_4 = x_63;
x_5 = x_62;
goto _start;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint64_t x_72; lean_object* x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; lean_object* x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; size_t x_81; size_t x_82; lean_object* x_83; size_t x_84; size_t x_85; size_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; size_t x_97; 
x_65 = lean_ctor_get(x_16, 0);
x_66 = lean_ctor_get(x_16, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_16);
x_67 = lean_ctor_get(x_1, 1);
x_68 = l_instInhabitedNat;
x_69 = lean_box(x_7);
lean_ctor_set(x_9, 1, x_69);
lean_ctor_set(x_9, 0, x_6);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_9);
x_71 = lean_array_get_size(x_67);
x_72 = lean_uint64_of_nat(x_11);
x_73 = lean_unsigned_to_nat(32u);
x_74 = lean_uint64_of_nat(x_73);
x_75 = lean_uint64_shift_right(x_72, x_74);
x_76 = lean_uint64_xor(x_72, x_75);
x_77 = lean_unsigned_to_nat(16u);
x_78 = lean_uint64_of_nat(x_77);
x_79 = lean_uint64_shift_right(x_76, x_78);
x_80 = lean_uint64_xor(x_76, x_79);
x_81 = lean_uint64_to_usize(x_80);
x_82 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_83 = lean_unsigned_to_nat(1u);
x_84 = lean_usize_of_nat(x_83);
x_85 = lean_usize_sub(x_82, x_84);
x_86 = lean_usize_land(x_81, x_85);
x_87 = lean_array_uget(x_67, x_86);
x_88 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__6___redArg(x_70, x_11, x_87);
lean_dec(x_87);
lean_dec(x_11);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
x_93 = l_BitVec_ofNat(x_65, x_66);
lean_dec(x_66);
if (lean_is_scalar(x_90)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_90;
}
lean_ctor_set(x_94, 0, x_65);
lean_ctor_set(x_94, 1, x_93);
if (lean_is_scalar(x_92)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_92;
}
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_array_push(x_5, x_95);
x_97 = lean_usize_add(x_4, x_84);
x_4 = x_97;
x_5 = x_96;
goto _start;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint64_t x_114; lean_object* x_115; uint64_t x_116; uint64_t x_117; uint64_t x_118; lean_object* x_119; uint64_t x_120; uint64_t x_121; uint64_t x_122; size_t x_123; size_t x_124; lean_object* x_125; size_t x_126; size_t x_127; size_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; size_t x_139; 
x_99 = lean_ctor_get(x_9, 0);
x_100 = lean_ctor_get(x_9, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_9);
x_101 = lean_unsigned_to_nat(0u);
x_102 = l_Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2___redArg(x_100);
lean_dec(x_100);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_101);
lean_inc(x_102);
x_104 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4___redArg(x_102, x_102, x_103);
lean_dec(x_102);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_1, 1);
x_109 = l_instInhabitedNat;
x_110 = lean_box(x_7);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_6);
lean_ctor_set(x_111, 1, x_110);
if (lean_is_scalar(x_107)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_107;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_array_get_size(x_108);
x_114 = lean_uint64_of_nat(x_99);
x_115 = lean_unsigned_to_nat(32u);
x_116 = lean_uint64_of_nat(x_115);
x_117 = lean_uint64_shift_right(x_114, x_116);
x_118 = lean_uint64_xor(x_114, x_117);
x_119 = lean_unsigned_to_nat(16u);
x_120 = lean_uint64_of_nat(x_119);
x_121 = lean_uint64_shift_right(x_118, x_120);
x_122 = lean_uint64_xor(x_118, x_121);
x_123 = lean_uint64_to_usize(x_122);
x_124 = lean_usize_of_nat(x_113);
lean_dec(x_113);
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_usize_of_nat(x_125);
x_127 = lean_usize_sub(x_124, x_126);
x_128 = lean_usize_land(x_123, x_127);
x_129 = lean_array_uget(x_108, x_128);
x_130 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__6___redArg(x_112, x_99, x_129);
lean_dec(x_129);
lean_dec(x_99);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_134 = x_131;
} else {
 lean_dec_ref(x_131);
 x_134 = lean_box(0);
}
x_135 = l_BitVec_ofNat(x_105, x_106);
lean_dec(x_106);
if (lean_is_scalar(x_132)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_132;
}
lean_ctor_set(x_136, 0, x_105);
lean_ctor_set(x_136, 1, x_135);
if (lean_is_scalar(x_134)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_134;
}
lean_ctor_set(x_137, 0, x_133);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_array_push(x_5, x_137);
x_139 = lean_usize_add(x_4, x_126);
x_4 = x_139;
x_5 = x_138;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__9(lean_object* x_1, lean_object* x_2) {
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
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_array_push(x_1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__9(x_4, x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_filter_go___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_instInhabitedExpr;
x_5 = l_instInhabitedBool;
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; size_t x_26; size_t x_27; lean_object* x_28; size_t x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_3, 2);
x_10 = lean_ctor_get(x_1, 1);
x_11 = l_instInhabitedNat;
x_12 = lean_box(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_array_get_size(x_10);
x_17 = lean_uint64_of_nat(x_15);
x_18 = lean_unsigned_to_nat(32u);
x_19 = lean_uint64_of_nat(x_18);
x_20 = lean_uint64_shift_right(x_17, x_19);
x_21 = lean_uint64_xor(x_17, x_20);
x_22 = lean_unsigned_to_nat(16u);
x_23 = lean_uint64_of_nat(x_22);
x_24 = lean_uint64_shift_right(x_21, x_23);
x_25 = lean_uint64_xor(x_21, x_24);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_usize_sub(x_27, x_29);
x_31 = lean_usize_land(x_26, x_30);
x_32 = lean_array_uget(x_10, x_31);
x_33 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__6___redArg(x_14, x_15, x_32);
lean_dec(x_32);
lean_dec(x_15);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_ctor_set(x_3, 2, x_2);
x_2 = x_3;
x_3 = x_9;
goto _start;
}
else
{
lean_free_object(x_3);
lean_dec(x_8);
lean_dec(x_7);
x_3 = x_9;
goto _start;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; lean_object* x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; size_t x_58; size_t x_59; lean_object* x_60; size_t x_61; size_t x_62; size_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_39 = lean_ctor_get(x_3, 0);
x_40 = lean_ctor_get(x_3, 1);
x_41 = lean_ctor_get(x_3, 2);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_3);
x_42 = lean_ctor_get(x_1, 1);
x_43 = l_instInhabitedNat;
x_44 = lean_box(x_5);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_ctor_get(x_39, 0);
lean_inc(x_47);
x_48 = lean_array_get_size(x_42);
x_49 = lean_uint64_of_nat(x_47);
x_50 = lean_unsigned_to_nat(32u);
x_51 = lean_uint64_of_nat(x_50);
x_52 = lean_uint64_shift_right(x_49, x_51);
x_53 = lean_uint64_xor(x_49, x_52);
x_54 = lean_unsigned_to_nat(16u);
x_55 = lean_uint64_of_nat(x_54);
x_56 = lean_uint64_shift_right(x_53, x_55);
x_57 = lean_uint64_xor(x_53, x_56);
x_58 = lean_uint64_to_usize(x_57);
x_59 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_usize_of_nat(x_60);
x_62 = lean_usize_sub(x_59, x_61);
x_63 = lean_usize_land(x_58, x_62);
x_64 = lean_array_uget(x_42, x_63);
x_65 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__6___redArg(x_46, x_47, x_64);
lean_dec(x_64);
lean_dec(x_47);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_39);
lean_ctor_set(x_69, 1, x_40);
lean_ctor_set(x_69, 2, x_2);
x_2 = x_69;
x_3 = x_41;
goto _start;
}
else
{
lean_dec(x_40);
lean_dec(x_39);
x_3 = x_41;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = lean_box(0);
x_10 = l_Std_DHashMap_Internal_AssocList_filter_go___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__11(x_1, x_9, x_6);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_3, x_12);
x_14 = lean_array_uset(x_8, x_3, x_10);
x_3 = x_13;
x_4 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__13(lean_object* x_1, lean_object* x_2) {
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
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_array_push(x_1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__14(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__13(x_4, x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__15(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_length___redArg(x_6);
lean_dec(x_6);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_unsigned_to_nat(8u);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_shiftl(x_11, x_12);
x_14 = lean_unsigned_to_nat(3u);
x_15 = lean_nat_div(x_13, x_14);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_48; uint8_t x_49; 
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 0);
lean_dec(x_18);
x_19 = l_Nat_nextPowerOfTwo(x_15);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_mk_array(x_19, x_20);
lean_ctor_set(x_1, 1, x_22);
lean_ctor_set(x_1, 0, x_21);
x_37 = lean_array_size(x_17);
x_38 = lean_usize_of_nat(x_21);
x_39 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__12(x_4, x_37, x_38, x_17);
x_48 = lean_array_get_size(x_39);
x_49 = lean_nat_dec_lt(x_21, x_48);
if (x_49 == 0)
{
lean_dec(x_48);
x_40 = x_21;
goto block_47;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_48, x_48);
if (x_50 == 0)
{
lean_dec(x_48);
x_40 = x_21;
goto block_47;
}
else
{
size_t x_51; lean_object* x_52; 
x_51 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_52 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__15(x_39, x_38, x_51, x_21);
x_40 = x_52;
goto block_47;
}
}
block_36:
{
size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_24 = lean_array_size(x_23);
x_25 = lean_usize_of_nat(x_21);
x_26 = lean_mk_empty_array_with_capacity(x_21);
x_27 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__7(x_3, x_2, x_23, x_24, x_25, x_1);
lean_dec(x_23);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_mk_empty_array_with_capacity(x_28);
lean_dec(x_28);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_array_get_size(x_30);
x_32 = lean_nat_dec_lt(x_21, x_31);
if (x_32 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
x_5 = x_26;
x_6 = x_25;
x_7 = x_29;
goto block_10;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_31, x_31);
if (x_33 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
x_5 = x_26;
x_6 = x_25;
x_7 = x_29;
goto block_10;
}
else
{
size_t x_34; lean_object* x_35; 
x_34 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_35 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__10(x_30, x_25, x_34, x_29);
lean_dec(x_30);
x_5 = x_26;
x_6 = x_25;
x_7 = x_35;
goto block_10;
}
}
}
block_47:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_mk_empty_array_with_capacity(x_40);
lean_dec(x_40);
x_42 = lean_array_get_size(x_39);
x_43 = lean_nat_dec_lt(x_21, x_42);
if (x_43 == 0)
{
lean_dec(x_42);
lean_dec(x_39);
x_23 = x_41;
goto block_36;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_le(x_42, x_42);
if (x_44 == 0)
{
lean_dec(x_42);
lean_dec(x_39);
x_23 = x_41;
goto block_36;
}
else
{
size_t x_45; lean_object* x_46; 
x_45 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_46 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__14(x_39, x_38, x_45, x_41);
lean_dec(x_39);
x_23 = x_46;
goto block_36;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_84; uint8_t x_85; 
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
lean_dec(x_1);
x_54 = l_Nat_nextPowerOfTwo(x_15);
lean_dec(x_15);
x_55 = lean_box(0);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_mk_array(x_54, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_73 = lean_array_size(x_53);
x_74 = lean_usize_of_nat(x_56);
x_75 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__12(x_4, x_73, x_74, x_53);
x_84 = lean_array_get_size(x_75);
x_85 = lean_nat_dec_lt(x_56, x_84);
if (x_85 == 0)
{
lean_dec(x_84);
x_76 = x_56;
goto block_83;
}
else
{
uint8_t x_86; 
x_86 = lean_nat_dec_le(x_84, x_84);
if (x_86 == 0)
{
lean_dec(x_84);
x_76 = x_56;
goto block_83;
}
else
{
size_t x_87; lean_object* x_88; 
x_87 = lean_usize_of_nat(x_84);
lean_dec(x_84);
x_88 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__15(x_75, x_74, x_87, x_56);
x_76 = x_88;
goto block_83;
}
}
block_72:
{
size_t x_60; size_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_60 = lean_array_size(x_59);
x_61 = lean_usize_of_nat(x_56);
x_62 = lean_mk_empty_array_with_capacity(x_56);
x_63 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__7(x_3, x_2, x_59, x_60, x_61, x_58);
lean_dec(x_59);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_mk_empty_array_with_capacity(x_64);
lean_dec(x_64);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_array_get_size(x_66);
x_68 = lean_nat_dec_lt(x_56, x_67);
if (x_68 == 0)
{
lean_dec(x_67);
lean_dec(x_66);
x_5 = x_62;
x_6 = x_61;
x_7 = x_65;
goto block_10;
}
else
{
uint8_t x_69; 
x_69 = lean_nat_dec_le(x_67, x_67);
if (x_69 == 0)
{
lean_dec(x_67);
lean_dec(x_66);
x_5 = x_62;
x_6 = x_61;
x_7 = x_65;
goto block_10;
}
else
{
size_t x_70; lean_object* x_71; 
x_70 = lean_usize_of_nat(x_67);
lean_dec(x_67);
x_71 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__10(x_66, x_61, x_70, x_65);
lean_dec(x_66);
x_5 = x_62;
x_6 = x_61;
x_7 = x_71;
goto block_10;
}
}
}
block_83:
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_mk_empty_array_with_capacity(x_76);
lean_dec(x_76);
x_78 = lean_array_get_size(x_75);
x_79 = lean_nat_dec_lt(x_56, x_78);
if (x_79 == 0)
{
lean_dec(x_78);
lean_dec(x_75);
x_59 = x_77;
goto block_72;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_le(x_78, x_78);
if (x_80 == 0)
{
lean_dec(x_78);
lean_dec(x_75);
x_59 = x_77;
goto block_72;
}
else
{
size_t x_81; lean_object* x_82; 
x_81 = lean_usize_of_nat(x_78);
lean_dec(x_78);
x_82 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__14(x_75, x_74, x_81, x_77);
lean_dec(x_75);
x_59 = x_82;
goto block_72;
}
}
}
}
block_10:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_array_size(x_7);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__8(x_4, x_7, x_8, x_6, x_5);
lean_dec(x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at___Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_revFold___at___Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at___Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_revFold___at___Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBMap_toList___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4_spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__6___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__7(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__8(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__9(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__10(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_filter_go___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_filter_go___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__11(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__12(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__13___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__13(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__14(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample_spec__15(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_run___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_st_mk_ref(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = lean_apply_7(x_2, x_3, x_10, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_10, x_13);
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_10);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
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
lean_inc(x_15);
x_17 = lean_mk_array(x_15, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_box(0);
x_20 = lean_mk_array(x_15, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_empty_array_with_capacity(x_10);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_run___lam__0), 8, 3);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, x_1);
lean_closure_set(x_24, 2, x_2);
x_25 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_8, x_24, x_3, x_4, x_5, x_6, x_7);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_run(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_unusedHyps___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_unusedHyps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_unusedHyps___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_unusedHyps___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_unusedHyps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_unusedHyps(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_equations___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_equations(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_equations___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_equations___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_equations___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_equations(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addUninterpretedSymbol___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_22; uint64_t x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; size_t x_32; size_t x_33; lean_object* x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; uint8_t x_39; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Expr_eqv___boxed), 2, 0);
x_11 = lean_box(0);
x_22 = lean_array_get_size(x_9);
x_23 = l_Lean_Expr_hash(x_1);
x_24 = lean_unsigned_to_nat(32u);
x_25 = lean_uint64_of_nat(x_24);
x_26 = lean_uint64_shift_right(x_23, x_25);
x_27 = lean_uint64_xor(x_23, x_26);
x_28 = lean_unsigned_to_nat(16u);
x_29 = lean_uint64_of_nat(x_28);
x_30 = lean_uint64_shift_right(x_27, x_29);
x_31 = lean_uint64_xor(x_27, x_30);
x_32 = lean_uint64_to_usize(x_31);
x_33 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_usize_of_nat(x_34);
x_36 = lean_usize_sub(x_33, x_35);
x_37 = lean_usize_land(x_32, x_36);
x_38 = lean_array_uget(x_9, x_37);
lean_inc(x_38);
lean_inc(x_1);
x_39 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_10, x_1, x_38);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_6);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_41 = lean_ctor_get(x_6, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_6, 0);
lean_dec(x_42);
x_43 = lean_nat_add(x_8, x_34);
lean_dec(x_8);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_11);
lean_ctor_set(x_44, 2, x_38);
x_45 = lean_array_uset(x_9, x_37, x_44);
x_46 = lean_unsigned_to_nat(2u);
x_47 = lean_nat_shiftl(x_43, x_46);
x_48 = lean_unsigned_to_nat(3u);
x_49 = lean_nat_div(x_47, x_48);
lean_dec(x_47);
x_50 = lean_array_get_size(x_45);
x_51 = lean_nat_dec_le(x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_Lean_Expr_instHashable;
x_53 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_52, x_45);
lean_ctor_set(x_6, 1, x_53);
lean_ctor_set(x_6, 0, x_43);
x_12 = x_6;
goto block_21;
}
else
{
lean_ctor_set(x_6, 1, x_45);
lean_ctor_set(x_6, 0, x_43);
x_12 = x_6;
goto block_21;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_6);
x_54 = lean_nat_add(x_8, x_34);
lean_dec(x_8);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_11);
lean_ctor_set(x_55, 2, x_38);
x_56 = lean_array_uset(x_9, x_37, x_55);
x_57 = lean_unsigned_to_nat(2u);
x_58 = lean_nat_shiftl(x_54, x_57);
x_59 = lean_unsigned_to_nat(3u);
x_60 = lean_nat_div(x_58, x_59);
lean_dec(x_58);
x_61 = lean_array_get_size(x_56);
x_62 = lean_nat_dec_le(x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = l_Lean_Expr_instHashable;
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_63, x_56);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_54);
lean_ctor_set(x_65, 1, x_64);
x_12 = x_65;
goto block_21;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_56);
x_12 = x_66;
goto block_21;
}
}
}
else
{
lean_dec(x_38);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_12 = x_6;
goto block_21;
}
block_21:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 2);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_st_ref_set(x_2, x_15, x_7);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addUninterpretedSymbol(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_27; uint64_t x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; lean_object* x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; size_t x_37; size_t x_38; lean_object* x_39; size_t x_40; size_t x_41; size_t x_42; lean_object* x_43; uint8_t x_44; 
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_Lean_Expr_eqv___boxed), 2, 0);
x_16 = lean_box(0);
x_27 = lean_array_get_size(x_14);
x_28 = l_Lean_Expr_hash(x_1);
x_29 = lean_unsigned_to_nat(32u);
x_30 = lean_uint64_of_nat(x_29);
x_31 = lean_uint64_shift_right(x_28, x_30);
x_32 = lean_uint64_xor(x_28, x_31);
x_33 = lean_unsigned_to_nat(16u);
x_34 = lean_uint64_of_nat(x_33);
x_35 = lean_uint64_shift_right(x_32, x_34);
x_36 = lean_uint64_xor(x_32, x_35);
x_37 = lean_uint64_to_usize(x_36);
x_38 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_usize_of_nat(x_39);
x_41 = lean_usize_sub(x_38, x_40);
x_42 = lean_usize_land(x_37, x_41);
x_43 = lean_array_uget(x_14, x_42);
lean_inc(x_43);
lean_inc(x_1);
x_44 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_15, x_1, x_43);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_11);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_46 = lean_ctor_get(x_11, 1);
lean_dec(x_46);
x_47 = lean_ctor_get(x_11, 0);
lean_dec(x_47);
x_48 = lean_nat_add(x_13, x_39);
lean_dec(x_13);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_16);
lean_ctor_set(x_49, 2, x_43);
x_50 = lean_array_uset(x_14, x_42, x_49);
x_51 = lean_unsigned_to_nat(2u);
x_52 = lean_nat_shiftl(x_48, x_51);
x_53 = lean_unsigned_to_nat(3u);
x_54 = lean_nat_div(x_52, x_53);
lean_dec(x_52);
x_55 = lean_array_get_size(x_50);
x_56 = lean_nat_dec_le(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Lean_Expr_instHashable;
x_58 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_57, x_50);
lean_ctor_set(x_11, 1, x_58);
lean_ctor_set(x_11, 0, x_48);
x_17 = x_11;
goto block_26;
}
else
{
lean_ctor_set(x_11, 1, x_50);
lean_ctor_set(x_11, 0, x_48);
x_17 = x_11;
goto block_26;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_11);
x_59 = lean_nat_add(x_13, x_39);
lean_dec(x_13);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_16);
lean_ctor_set(x_60, 2, x_43);
x_61 = lean_array_uset(x_14, x_42, x_60);
x_62 = lean_unsigned_to_nat(2u);
x_63 = lean_nat_shiftl(x_59, x_62);
x_64 = lean_unsigned_to_nat(3u);
x_65 = lean_nat_div(x_63, x_64);
lean_dec(x_63);
x_66 = lean_array_get_size(x_61);
x_67 = lean_nat_dec_le(x_65, x_66);
lean_dec(x_66);
lean_dec(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = l_Lean_Expr_instHashable;
x_69 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_68, x_61);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_59);
lean_ctor_set(x_70, 1, x_69);
x_17 = x_70;
goto block_26;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_59);
lean_ctor_set(x_71, 1, x_61);
x_17 = x_71;
goto block_26;
}
}
}
else
{
lean_dec(x_43);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_17 = x_11;
goto block_26;
}
block_26:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 2);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_st_ref_set(x_3, x_20, x_12);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_16);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addUninterpretedSymbol___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addUninterpretedSymbol___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addUninterpretedSymbol___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addUninterpretedSymbol(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addUnusedRelevantHypothesis___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_22; uint64_t x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; size_t x_32; size_t x_33; lean_object* x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; uint8_t x_39; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = l_Lean_instBEqFVarId;
x_12 = lean_box(0);
x_22 = lean_array_get_size(x_9);
x_23 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_24 = lean_unsigned_to_nat(32u);
x_25 = lean_uint64_of_nat(x_24);
x_26 = lean_uint64_shift_right(x_23, x_25);
x_27 = lean_uint64_xor(x_23, x_26);
x_28 = lean_unsigned_to_nat(16u);
x_29 = lean_uint64_of_nat(x_28);
x_30 = lean_uint64_shift_right(x_27, x_29);
x_31 = lean_uint64_xor(x_27, x_30);
x_32 = lean_uint64_to_usize(x_31);
x_33 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_usize_of_nat(x_34);
x_36 = lean_usize_sub(x_33, x_35);
x_37 = lean_usize_land(x_32, x_36);
x_38 = lean_array_uget(x_9, x_37);
lean_inc(x_38);
lean_inc(x_1);
x_39 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_11, x_1, x_38);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_6);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_41 = lean_ctor_get(x_6, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_6, 0);
lean_dec(x_42);
x_43 = lean_nat_add(x_8, x_34);
lean_dec(x_8);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_12);
lean_ctor_set(x_44, 2, x_38);
x_45 = lean_array_uset(x_9, x_37, x_44);
x_46 = lean_unsigned_to_nat(2u);
x_47 = lean_nat_shiftl(x_43, x_46);
x_48 = lean_unsigned_to_nat(3u);
x_49 = lean_nat_div(x_47, x_48);
lean_dec(x_47);
x_50 = lean_array_get_size(x_45);
x_51 = lean_nat_dec_le(x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_Lean_instHashableFVarId;
x_53 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_52, x_45);
lean_ctor_set(x_6, 1, x_53);
lean_ctor_set(x_6, 0, x_43);
x_13 = x_6;
goto block_21;
}
else
{
lean_ctor_set(x_6, 1, x_45);
lean_ctor_set(x_6, 0, x_43);
x_13 = x_6;
goto block_21;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_6);
x_54 = lean_nat_add(x_8, x_34);
lean_dec(x_8);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_12);
lean_ctor_set(x_55, 2, x_38);
x_56 = lean_array_uset(x_9, x_37, x_55);
x_57 = lean_unsigned_to_nat(2u);
x_58 = lean_nat_shiftl(x_54, x_57);
x_59 = lean_unsigned_to_nat(3u);
x_60 = lean_nat_div(x_58, x_59);
lean_dec(x_58);
x_61 = lean_array_get_size(x_56);
x_62 = lean_nat_dec_le(x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = l_Lean_instHashableFVarId;
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_63, x_56);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_54);
lean_ctor_set(x_65, 1, x_64);
x_13 = x_65;
goto block_21;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_56);
x_13 = x_66;
goto block_21;
}
}
}
else
{
lean_dec(x_38);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_13 = x_6;
goto block_21;
}
block_21:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_5, 2);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_st_ref_set(x_2, x_15, x_7);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addUnusedRelevantHypothesis(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_27; uint64_t x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; lean_object* x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; size_t x_37; size_t x_38; lean_object* x_39; size_t x_40; size_t x_41; size_t x_42; lean_object* x_43; uint8_t x_44; 
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = l_Lean_instBEqFVarId;
x_17 = lean_box(0);
x_27 = lean_array_get_size(x_14);
x_28 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_29 = lean_unsigned_to_nat(32u);
x_30 = lean_uint64_of_nat(x_29);
x_31 = lean_uint64_shift_right(x_28, x_30);
x_32 = lean_uint64_xor(x_28, x_31);
x_33 = lean_unsigned_to_nat(16u);
x_34 = lean_uint64_of_nat(x_33);
x_35 = lean_uint64_shift_right(x_32, x_34);
x_36 = lean_uint64_xor(x_32, x_35);
x_37 = lean_uint64_to_usize(x_36);
x_38 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_usize_of_nat(x_39);
x_41 = lean_usize_sub(x_38, x_40);
x_42 = lean_usize_land(x_37, x_41);
x_43 = lean_array_uget(x_14, x_42);
lean_inc(x_43);
lean_inc(x_1);
x_44 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_16, x_1, x_43);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_11);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_46 = lean_ctor_get(x_11, 1);
lean_dec(x_46);
x_47 = lean_ctor_get(x_11, 0);
lean_dec(x_47);
x_48 = lean_nat_add(x_13, x_39);
lean_dec(x_13);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_17);
lean_ctor_set(x_49, 2, x_43);
x_50 = lean_array_uset(x_14, x_42, x_49);
x_51 = lean_unsigned_to_nat(2u);
x_52 = lean_nat_shiftl(x_48, x_51);
x_53 = lean_unsigned_to_nat(3u);
x_54 = lean_nat_div(x_52, x_53);
lean_dec(x_52);
x_55 = lean_array_get_size(x_50);
x_56 = lean_nat_dec_le(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Lean_instHashableFVarId;
x_58 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_57, x_50);
lean_ctor_set(x_11, 1, x_58);
lean_ctor_set(x_11, 0, x_48);
x_18 = x_11;
goto block_26;
}
else
{
lean_ctor_set(x_11, 1, x_50);
lean_ctor_set(x_11, 0, x_48);
x_18 = x_11;
goto block_26;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_11);
x_59 = lean_nat_add(x_13, x_39);
lean_dec(x_13);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_17);
lean_ctor_set(x_60, 2, x_43);
x_61 = lean_array_uset(x_14, x_42, x_60);
x_62 = lean_unsigned_to_nat(2u);
x_63 = lean_nat_shiftl(x_59, x_62);
x_64 = lean_unsigned_to_nat(3u);
x_65 = lean_nat_div(x_63, x_64);
lean_dec(x_63);
x_66 = lean_array_get_size(x_61);
x_67 = lean_nat_dec_le(x_65, x_66);
lean_dec(x_66);
lean_dec(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = l_Lean_instHashableFVarId;
x_69 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_68, x_61);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_59);
lean_ctor_set(x_70, 1, x_69);
x_18 = x_70;
goto block_26;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_59);
lean_ctor_set(x_71, 1, x_61);
x_18 = x_71;
goto block_26;
}
}
}
else
{
lean_dec(x_43);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_18 = x_11;
goto block_26;
}
block_26:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_10, 2);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_st_ref_set(x_3, x_20, x_12);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_17);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addUnusedRelevantHypothesis___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addUnusedRelevantHypothesis___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addUnusedRelevantHypothesis___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addUnusedRelevantHypothesis(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addDerivedEquation___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 2);
lean_inc(x_11);
lean_dec(x_7);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 0, x_1);
x_12 = lean_array_push(x_11, x_5);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_st_ref_set(x_3, x_13, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_5);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 2);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_2);
x_27 = lean_array_push(x_25, x_26);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_st_ref_set(x_3, x_28, x_22);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addDerivedEquation(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 2);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set(x_10, 0, x_1);
x_17 = lean_array_push(x_16, x_10);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_st_ref_set(x_4, x_18, x_13);
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
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 2);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_2);
x_32 = lean_array_push(x_30, x_31);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_st_ref_set(x_4, x_33, x_27);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addDerivedEquation___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addDerivedEquation___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addDerivedEquation___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_addDerivedEquation(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_forInStep_go___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_ctor_get(x_2, 1);
lean_dec(x_14);
lean_inc(x_5);
lean_inc(x_12);
x_15 = l_Lean_FVarId_getType___redArg(x_12, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0(x_1, x_16);
lean_dec(x_16);
if (x_19 == 0)
{
lean_free_object(x_2);
lean_dec(x_12);
x_2 = x_13;
x_3 = x_18;
x_8 = x_17;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_35; uint64_t x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; lean_object* x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; size_t x_45; size_t x_46; lean_object* x_47; size_t x_48; size_t x_49; size_t x_50; lean_object* x_51; uint8_t x_52; 
x_21 = lean_st_ref_take(x_4, x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
x_35 = lean_array_get_size(x_26);
x_36 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_12);
x_37 = lean_unsigned_to_nat(32u);
x_38 = lean_uint64_of_nat(x_37);
x_39 = lean_uint64_shift_right(x_36, x_38);
x_40 = lean_uint64_xor(x_36, x_39);
x_41 = lean_unsigned_to_nat(16u);
x_42 = lean_uint64_of_nat(x_41);
x_43 = lean_uint64_shift_right(x_40, x_42);
x_44 = lean_uint64_xor(x_40, x_43);
x_45 = lean_uint64_to_usize(x_44);
x_46 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_usize_of_nat(x_47);
x_49 = lean_usize_sub(x_46, x_48);
x_50 = lean_usize_land(x_45, x_49);
x_51 = lean_array_uget(x_26, x_50);
x_52 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_MVarId_getNondepPropHyps_spec__0___redArg(x_12, x_51);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_23);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_ctor_get(x_23, 1);
lean_dec(x_54);
x_55 = lean_ctor_get(x_23, 0);
lean_dec(x_55);
x_56 = lean_nat_add(x_25, x_47);
lean_dec(x_25);
lean_ctor_set(x_2, 2, x_51);
lean_ctor_set(x_2, 1, x_18);
x_57 = lean_array_uset(x_26, x_50, x_2);
x_58 = lean_unsigned_to_nat(2u);
x_59 = lean_nat_shiftl(x_56, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_MVarId_getNondepPropHyps_spec__6___redArg(x_57);
lean_ctor_set(x_23, 1, x_64);
lean_ctor_set(x_23, 0, x_56);
x_28 = x_23;
goto block_34;
}
else
{
lean_ctor_set(x_23, 1, x_57);
lean_ctor_set(x_23, 0, x_56);
x_28 = x_23;
goto block_34;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_23);
x_65 = lean_nat_add(x_25, x_47);
lean_dec(x_25);
lean_ctor_set(x_2, 2, x_51);
lean_ctor_set(x_2, 1, x_18);
x_66 = lean_array_uset(x_26, x_50, x_2);
x_67 = lean_unsigned_to_nat(2u);
x_68 = lean_nat_shiftl(x_65, x_67);
x_69 = lean_unsigned_to_nat(3u);
x_70 = lean_nat_div(x_68, x_69);
lean_dec(x_68);
x_71 = lean_array_get_size(x_66);
x_72 = lean_nat_dec_le(x_70, x_71);
lean_dec(x_71);
lean_dec(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_MVarId_getNondepPropHyps_spec__6___redArg(x_66);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_65);
lean_ctor_set(x_74, 1, x_73);
x_28 = x_74;
goto block_34;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_65);
lean_ctor_set(x_75, 1, x_66);
x_28 = x_75;
goto block_34;
}
}
}
else
{
lean_dec(x_51);
lean_dec(x_26);
lean_dec(x_25);
lean_free_object(x_2);
lean_dec(x_12);
x_28 = x_23;
goto block_34;
}
block_34:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_22, 2);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_st_ref_set(x_4, x_30, x_24);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_2 = x_13;
x_3 = x_18;
x_8 = x_32;
goto _start;
}
}
}
else
{
uint8_t x_76; 
lean_free_object(x_2);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_76 = !lean_is_exclusive(x_15);
if (x_76 == 0)
{
return x_15;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_15, 0);
x_78 = lean_ctor_get(x_15, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_15);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_2, 0);
x_81 = lean_ctor_get(x_2, 2);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_2);
lean_inc(x_5);
lean_inc(x_80);
x_82 = l_Lean_FVarId_getType___redArg(x_80, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_box(0);
x_86 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Expr_containsFVar_spec__0(x_1, x_83);
lean_dec(x_83);
if (x_86 == 0)
{
lean_dec(x_80);
x_2 = x_81;
x_3 = x_85;
x_8 = x_84;
goto _start;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_102; uint64_t x_103; lean_object* x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; size_t x_112; size_t x_113; lean_object* x_114; size_t x_115; size_t x_116; size_t x_117; lean_object* x_118; uint8_t x_119; 
x_88 = lean_st_ref_take(x_4, x_84);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
x_102 = lean_array_get_size(x_93);
x_103 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_80);
x_104 = lean_unsigned_to_nat(32u);
x_105 = lean_uint64_of_nat(x_104);
x_106 = lean_uint64_shift_right(x_103, x_105);
x_107 = lean_uint64_xor(x_103, x_106);
x_108 = lean_unsigned_to_nat(16u);
x_109 = lean_uint64_of_nat(x_108);
x_110 = lean_uint64_shift_right(x_107, x_109);
x_111 = lean_uint64_xor(x_107, x_110);
x_112 = lean_uint64_to_usize(x_111);
x_113 = lean_usize_of_nat(x_102);
lean_dec(x_102);
x_114 = lean_unsigned_to_nat(1u);
x_115 = lean_usize_of_nat(x_114);
x_116 = lean_usize_sub(x_113, x_115);
x_117 = lean_usize_land(x_112, x_116);
x_118 = lean_array_uget(x_93, x_117);
x_119 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_MVarId_getNondepPropHyps_spec__0___redArg(x_80, x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_120 = x_90;
} else {
 lean_dec_ref(x_90);
 x_120 = lean_box(0);
}
x_121 = lean_nat_add(x_92, x_114);
lean_dec(x_92);
x_122 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_122, 0, x_80);
lean_ctor_set(x_122, 1, x_85);
lean_ctor_set(x_122, 2, x_118);
x_123 = lean_array_uset(x_93, x_117, x_122);
x_124 = lean_unsigned_to_nat(2u);
x_125 = lean_nat_shiftl(x_121, x_124);
x_126 = lean_unsigned_to_nat(3u);
x_127 = lean_nat_div(x_125, x_126);
lean_dec(x_125);
x_128 = lean_array_get_size(x_123);
x_129 = lean_nat_dec_le(x_127, x_128);
lean_dec(x_128);
lean_dec(x_127);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_MVarId_getNondepPropHyps_spec__6___redArg(x_123);
if (lean_is_scalar(x_120)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_120;
}
lean_ctor_set(x_131, 0, x_121);
lean_ctor_set(x_131, 1, x_130);
x_95 = x_131;
goto block_101;
}
else
{
lean_object* x_132; 
if (lean_is_scalar(x_120)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_120;
}
lean_ctor_set(x_132, 0, x_121);
lean_ctor_set(x_132, 1, x_123);
x_95 = x_132;
goto block_101;
}
}
else
{
lean_dec(x_118);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_80);
x_95 = x_90;
goto block_101;
}
block_101:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_89, 2);
lean_inc(x_96);
lean_dec(x_89);
x_97 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
lean_ctor_set(x_97, 2, x_96);
x_98 = lean_st_ref_set(x_4, x_97, x_91);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_2 = x_81;
x_3 = x_85;
x_8 = x_99;
goto _start;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_5);
x_133 = lean_ctor_get(x_82, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_82, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_135 = x_82;
} else {
 lean_dec_ref(x_82);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_forInStep_go___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_DHashMap_Internal_AssocList_forInStep_go___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(x_1, x_2, x_3, x_5, x_6, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_uget(x_2, x_4);
lean_inc(x_8);
x_16 = l_Std_DHashMap_Internal_AssocList_forInStep_go___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(x_1, x_15, x_5, x_7, x_8, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_8);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_usize_of_nat(x_26);
x_28 = lean_usize_add(x_4, x_27);
x_4 = x_28;
x_5 = x_25;
x_12 = x_24;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_8);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; size_t x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_box(0);
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_array_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_usize_of_nat(x_13);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed_spec__1(x_1, x_11, x_12, x_14, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_10);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_forInStep_go___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_forInStep_go___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_forInStep_go___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_DHashMap_Internal_AssocList_forInStep_go___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed_spec__1(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
lean_inc(x_1);
x_16 = l_Lean_Environment_find_x3f(x_13, x_1, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_9);
x_17 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = lean_unbox(x_14);
x_20 = l_Lean_MessageData_ofConstName(x_1, x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked("'", 1, 1);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(x_24, x_4, x_5, x_6, x_7, x_12);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_1);
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
lean_dec(x_16);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(0);
x_31 = lean_unbox(x_30);
lean_inc(x_1);
x_32 = l_Lean_Environment_find_x3f(x_29, x_1, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_34 = l_Lean_stringToMessageData(x_33);
lean_dec(x_33);
x_35 = lean_unbox(x_30);
x_36 = l_Lean_MessageData_ofConstName(x_1, x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_mk_string_unchecked("'", 1, 1);
x_39 = l_Lean_stringToMessageData(x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(x_40, x_4, x_5, x_6, x_7, x_28);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_1);
x_42 = lean_ctor_get(x_32, 0);
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_28);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__2___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_13 = l_instMonadEIO(lean_box(0));
x_14 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_26, 0, lean_box(0));
lean_closure_set(x_26, 1, lean_box(0));
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_28, 0, x_27);
lean_inc(x_28);
lean_inc(x_25);
lean_inc(x_22);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_11);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_12);
x_31 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_33);
x_34 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_34, 0, x_33);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_35, 0, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_22);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_39, 0, x_25);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_41, 0, x_28);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_9);
lean_ctor_set(x_43, 2, x_38);
lean_ctor_set(x_43, 3, x_40);
lean_ctor_set(x_43, 4, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_10);
x_45 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_44);
x_46 = l_Lean_instInhabitedExpr;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_instInhabitedOfMonad___redArg(x_45, x_47);
x_49 = lean_alloc_closure((void*)(l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(x_49, 0, x_48);
x_50 = lean_panic_fn(x_49, x_1);
x_51 = lean_apply_7(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_51;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_mk_string_unchecked("BitVec", 6, 6);
x_14 = lean_mk_string_unchecked("ofNat", 5, 5);
x_15 = l_Lean_Name_mkStr2(x_13, x_14);
x_16 = lean_box(0);
x_17 = l_Lean_Expr_const___override(x_15, x_16);
lean_inc(x_11);
x_18 = l_Lean_mkNatLit(x_11);
x_19 = l_BitVec_toNat(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_20 = l_Lean_mkNatLit(x_19);
x_21 = l_Lean_mkAppB(x_17, x_18, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isFVar(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_169; uint8_t x_170; 
lean_inc(x_1);
x_11 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_6, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_169 = l_Lean_Expr_cleanupAnnotations(x_12);
x_170 = l_Lean_Expr_isApp(x_169);
if (x_170 == 0)
{
lean_dec(x_169);
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
goto block_168;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_176; lean_object* x_180; lean_object* x_184; lean_object* x_188; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
x_192 = l_Lean_Expr_appFnCleanup___redArg(x_169);
x_193 = lean_mk_string_unchecked("Int64", 5, 5);
x_194 = lean_mk_string_unchecked("toBitVec", 8, 8);
lean_inc(x_194);
lean_inc(x_193);
x_195 = l_Lean_Name_mkStr2(x_193, x_194);
x_196 = l_Lean_Expr_isConstOf(x_192, x_195);
lean_dec(x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; 
lean_dec(x_193);
x_197 = lean_mk_string_unchecked("Int32", 5, 5);
lean_inc(x_194);
lean_inc(x_197);
x_198 = l_Lean_Name_mkStr2(x_197, x_194);
x_199 = l_Lean_Expr_isConstOf(x_192, x_198);
lean_dec(x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; 
lean_dec(x_197);
x_200 = lean_mk_string_unchecked("Int16", 5, 5);
lean_inc(x_194);
lean_inc(x_200);
x_201 = l_Lean_Name_mkStr2(x_200, x_194);
x_202 = l_Lean_Expr_isConstOf(x_192, x_201);
lean_dec(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; 
lean_dec(x_200);
x_203 = lean_mk_string_unchecked("Int8", 4, 4);
lean_inc(x_194);
lean_inc(x_203);
x_204 = l_Lean_Name_mkStr2(x_203, x_194);
x_205 = l_Lean_Expr_isConstOf(x_192, x_204);
lean_dec(x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; 
lean_dec(x_203);
x_206 = lean_mk_string_unchecked("UInt64", 6, 6);
lean_inc(x_194);
lean_inc(x_206);
x_207 = l_Lean_Name_mkStr2(x_206, x_194);
x_208 = l_Lean_Expr_isConstOf(x_192, x_207);
lean_dec(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; 
lean_dec(x_206);
x_209 = lean_mk_string_unchecked("UInt32", 6, 6);
lean_inc(x_194);
lean_inc(x_209);
x_210 = l_Lean_Name_mkStr2(x_209, x_194);
x_211 = l_Lean_Expr_isConstOf(x_192, x_210);
lean_dec(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; 
lean_dec(x_209);
x_212 = lean_mk_string_unchecked("UInt16", 6, 6);
lean_inc(x_194);
lean_inc(x_212);
x_213 = l_Lean_Name_mkStr2(x_212, x_194);
x_214 = l_Lean_Expr_isConstOf(x_192, x_213);
lean_dec(x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; uint8_t x_217; 
lean_dec(x_212);
x_215 = lean_mk_string_unchecked("UInt8", 5, 5);
lean_inc(x_215);
x_216 = l_Lean_Name_mkStr2(x_215, x_194);
x_217 = l_Lean_Expr_isConstOf(x_192, x_216);
lean_dec(x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
lean_dec(x_215);
x_218 = lean_mk_string_unchecked("BitVec", 6, 6);
x_219 = lean_mk_string_unchecked("ofBool", 6, 6);
x_220 = l_Lean_Name_mkStr2(x_218, x_219);
x_221 = l_Lean_Expr_isConstOf(x_192, x_220);
lean_dec(x_220);
lean_dec(x_192);
if (x_221 == 0)
{
lean_dec(x_171);
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
goto block_168;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_222 = lean_ctor_get(x_2, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_2, 1);
lean_inc(x_223);
lean_dec(x_2);
x_224 = lean_unsigned_to_nat(1u);
x_225 = l_BitVec_ofNat(x_222, x_224);
lean_dec(x_222);
x_226 = lean_nat_dec_eq(x_223, x_225);
lean_dec(x_225);
lean_dec(x_223);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_227 = lean_mk_string_unchecked("Bool", 4, 4);
x_228 = lean_mk_string_unchecked("false", 5, 5);
x_229 = l_Lean_Name_mkStr2(x_227, x_228);
x_230 = lean_box(0);
x_231 = l_Lean_Expr_const___override(x_229, x_230);
x_188 = x_231;
goto block_191;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_232 = lean_mk_string_unchecked("Bool", 4, 4);
x_233 = lean_mk_string_unchecked("true", 4, 4);
x_234 = l_Lean_Name_mkStr2(x_232, x_233);
x_235 = lean_box(0);
x_236 = l_Lean_Expr_const___override(x_234, x_235);
x_188 = x_236;
goto block_191;
}
}
}
else
{
lean_object* x_237; lean_object* x_238; uint8_t x_239; 
lean_dec(x_192);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_237 = lean_ctor_get(x_2, 0);
lean_inc(x_237);
x_238 = lean_unsigned_to_nat(8u);
x_239 = lean_nat_dec_eq(x_237, x_238);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_215);
lean_dec(x_171);
lean_dec(x_2);
x_240 = lean_mk_string_unchecked("Value for UInt8 was not 8 bit but ", 34, 34);
x_241 = l_Lean_stringToMessageData(x_240);
lean_dec(x_240);
x_242 = l___private_Init_Data_Repr_0__Nat_reprFast(x_237);
x_243 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_243, 0, x_242);
x_244 = l_Lean_MessageData_ofFormat(x_243);
x_245 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_245, 0, x_241);
lean_ctor_set(x_245, 1, x_244);
x_246 = lean_mk_string_unchecked(" bit", 4, 4);
x_247 = l_Lean_stringToMessageData(x_246);
lean_dec(x_246);
x_248 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_247);
x_249 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(x_248, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_249;
}
else
{
lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_250 = lean_ctor_get(x_2, 1);
lean_inc(x_250);
lean_dec(x_2);
x_251 = lean_uint8_of_nat_mk(x_250);
x_252 = lean_uint8_to_nat(x_251);
x_253 = l_Lean_mkRawNatLit(x_252);
x_254 = lean_mk_string_unchecked("OfNat", 5, 5);
x_255 = lean_mk_string_unchecked("ofNat", 5, 5);
x_256 = l_Lean_Name_mkStr2(x_254, x_255);
x_257 = lean_unsigned_to_nat(0u);
x_258 = l_Lean_Level_ofNat(x_257);
x_259 = lean_box(0);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
x_261 = l_Lean_Expr_const___override(x_256, x_260);
lean_inc(x_215);
x_262 = l_Lean_Name_mkStr1(x_215);
x_263 = l_Lean_Expr_const___override(x_262, x_259);
x_264 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_265 = l_Lean_Name_mkStr2(x_215, x_264);
x_266 = l_Lean_Expr_const___override(x_265, x_259);
lean_inc(x_253);
x_267 = l_Lean_Expr_app___override(x_266, x_253);
x_268 = l_Lean_mkApp3(x_261, x_263, x_253, x_267);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_171);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_13);
return x_270;
}
}
}
else
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; 
lean_dec(x_194);
lean_dec(x_192);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_271 = lean_ctor_get(x_2, 0);
lean_inc(x_271);
x_272 = lean_unsigned_to_nat(16u);
x_273 = lean_nat_dec_eq(x_271, x_272);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_212);
lean_dec(x_171);
lean_dec(x_2);
x_274 = lean_mk_string_unchecked("Value for UInt16 was not 16 bit but ", 36, 36);
x_275 = l_Lean_stringToMessageData(x_274);
lean_dec(x_274);
x_276 = l___private_Init_Data_Repr_0__Nat_reprFast(x_271);
x_277 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_277, 0, x_276);
x_278 = l_Lean_MessageData_ofFormat(x_277);
x_279 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_279, 0, x_275);
lean_ctor_set(x_279, 1, x_278);
x_280 = lean_mk_string_unchecked(" bit", 4, 4);
x_281 = l_Lean_stringToMessageData(x_280);
lean_dec(x_280);
x_282 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_281);
x_283 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(x_282, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_283;
}
else
{
lean_object* x_284; uint16_t x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_271);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_284 = lean_ctor_get(x_2, 1);
lean_inc(x_284);
lean_dec(x_2);
x_285 = lean_uint16_of_nat_mk(x_284);
x_286 = lean_uint16_to_nat(x_285);
x_287 = l_Lean_mkRawNatLit(x_286);
x_288 = lean_mk_string_unchecked("OfNat", 5, 5);
x_289 = lean_mk_string_unchecked("ofNat", 5, 5);
x_290 = l_Lean_Name_mkStr2(x_288, x_289);
x_291 = lean_unsigned_to_nat(0u);
x_292 = l_Lean_Level_ofNat(x_291);
x_293 = lean_box(0);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
x_295 = l_Lean_Expr_const___override(x_290, x_294);
lean_inc(x_212);
x_296 = l_Lean_Name_mkStr1(x_212);
x_297 = l_Lean_Expr_const___override(x_296, x_293);
x_298 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_299 = l_Lean_Name_mkStr2(x_212, x_298);
x_300 = l_Lean_Expr_const___override(x_299, x_293);
lean_inc(x_287);
x_301 = l_Lean_Expr_app___override(x_300, x_287);
x_302 = l_Lean_mkApp3(x_295, x_297, x_287, x_301);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_171);
lean_ctor_set(x_303, 1, x_302);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_13);
return x_304;
}
}
}
else
{
lean_object* x_305; lean_object* x_306; uint8_t x_307; 
lean_dec(x_194);
lean_dec(x_192);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_305 = lean_ctor_get(x_2, 0);
lean_inc(x_305);
x_306 = lean_unsigned_to_nat(32u);
x_307 = lean_nat_dec_eq(x_305, x_306);
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_209);
lean_dec(x_171);
lean_dec(x_2);
x_308 = lean_mk_string_unchecked("Value for UInt32 was not 32 bit but ", 36, 36);
x_309 = l_Lean_stringToMessageData(x_308);
lean_dec(x_308);
x_310 = l___private_Init_Data_Repr_0__Nat_reprFast(x_305);
x_311 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_311, 0, x_310);
x_312 = l_Lean_MessageData_ofFormat(x_311);
x_313 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_313, 0, x_309);
lean_ctor_set(x_313, 1, x_312);
x_314 = lean_mk_string_unchecked(" bit", 4, 4);
x_315 = l_Lean_stringToMessageData(x_314);
lean_dec(x_314);
x_316 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_316, 0, x_313);
lean_ctor_set(x_316, 1, x_315);
x_317 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(x_316, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_317;
}
else
{
lean_object* x_318; uint32_t x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_305);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_318 = lean_ctor_get(x_2, 1);
lean_inc(x_318);
lean_dec(x_2);
x_319 = lean_uint32_of_nat_mk(x_318);
x_320 = lean_uint32_to_nat(x_319);
x_321 = l_Lean_mkRawNatLit(x_320);
x_322 = lean_mk_string_unchecked("OfNat", 5, 5);
x_323 = lean_mk_string_unchecked("ofNat", 5, 5);
x_324 = l_Lean_Name_mkStr2(x_322, x_323);
x_325 = lean_unsigned_to_nat(0u);
x_326 = l_Lean_Level_ofNat(x_325);
x_327 = lean_box(0);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
x_329 = l_Lean_Expr_const___override(x_324, x_328);
lean_inc(x_209);
x_330 = l_Lean_Name_mkStr1(x_209);
x_331 = l_Lean_Expr_const___override(x_330, x_327);
x_332 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_333 = l_Lean_Name_mkStr2(x_209, x_332);
x_334 = l_Lean_Expr_const___override(x_333, x_327);
lean_inc(x_321);
x_335 = l_Lean_Expr_app___override(x_334, x_321);
x_336 = l_Lean_mkApp3(x_329, x_331, x_321, x_335);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_171);
lean_ctor_set(x_337, 1, x_336);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_13);
return x_338;
}
}
}
else
{
lean_object* x_339; lean_object* x_340; uint8_t x_341; 
lean_dec(x_194);
lean_dec(x_192);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_339 = lean_ctor_get(x_2, 0);
lean_inc(x_339);
x_340 = lean_unsigned_to_nat(64u);
x_341 = lean_nat_dec_eq(x_339, x_340);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_206);
lean_dec(x_171);
lean_dec(x_2);
x_342 = lean_mk_string_unchecked("Value for UInt64 was not 64 bit but ", 36, 36);
x_343 = l_Lean_stringToMessageData(x_342);
lean_dec(x_342);
x_344 = l___private_Init_Data_Repr_0__Nat_reprFast(x_339);
x_345 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_345, 0, x_344);
x_346 = l_Lean_MessageData_ofFormat(x_345);
x_347 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_347, 0, x_343);
lean_ctor_set(x_347, 1, x_346);
x_348 = lean_mk_string_unchecked(" bit", 4, 4);
x_349 = l_Lean_stringToMessageData(x_348);
lean_dec(x_348);
x_350 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_349);
x_351 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(x_350, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_351;
}
else
{
lean_object* x_352; uint64_t x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_339);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_352 = lean_ctor_get(x_2, 1);
lean_inc(x_352);
lean_dec(x_2);
x_353 = lean_uint64_of_nat_mk(x_352);
x_354 = lean_uint64_to_nat(x_353);
x_355 = l_Lean_mkRawNatLit(x_354);
x_356 = lean_mk_string_unchecked("OfNat", 5, 5);
x_357 = lean_mk_string_unchecked("ofNat", 5, 5);
x_358 = l_Lean_Name_mkStr2(x_356, x_357);
x_359 = lean_unsigned_to_nat(0u);
x_360 = l_Lean_Level_ofNat(x_359);
x_361 = lean_box(0);
x_362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_361);
x_363 = l_Lean_Expr_const___override(x_358, x_362);
lean_inc(x_206);
x_364 = l_Lean_Name_mkStr1(x_206);
x_365 = l_Lean_Expr_const___override(x_364, x_361);
x_366 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_367 = l_Lean_Name_mkStr2(x_206, x_366);
x_368 = l_Lean_Expr_const___override(x_367, x_361);
lean_inc(x_355);
x_369 = l_Lean_Expr_app___override(x_368, x_355);
x_370 = l_Lean_mkApp3(x_363, x_365, x_355, x_369);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_171);
lean_ctor_set(x_371, 1, x_370);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_13);
return x_372;
}
}
}
else
{
lean_object* x_373; lean_object* x_374; uint8_t x_375; 
lean_dec(x_194);
lean_dec(x_192);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_373 = lean_ctor_get(x_2, 0);
lean_inc(x_373);
x_374 = lean_unsigned_to_nat(8u);
x_375 = lean_nat_dec_eq(x_373, x_374);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_203);
lean_dec(x_171);
lean_dec(x_2);
x_376 = lean_mk_string_unchecked("Value for Int8 was not 8 bit but ", 33, 33);
x_377 = l_Lean_stringToMessageData(x_376);
lean_dec(x_376);
x_378 = l___private_Init_Data_Repr_0__Nat_reprFast(x_373);
x_379 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_379, 0, x_378);
x_380 = l_Lean_MessageData_ofFormat(x_379);
x_381 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_381, 0, x_377);
lean_ctor_set(x_381, 1, x_380);
x_382 = lean_mk_string_unchecked(" bit", 4, 4);
x_383 = l_Lean_stringToMessageData(x_382);
lean_dec(x_382);
x_384 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_384, 0, x_381);
lean_ctor_set(x_384, 1, x_383);
x_385 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(x_384, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_385;
}
else
{
lean_object* x_386; uint8_t x_387; lean_object* x_388; uint8_t x_389; uint8_t x_390; 
lean_dec(x_373);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_386 = lean_ctor_get(x_2, 1);
lean_inc(x_386);
lean_dec(x_2);
x_387 = lean_uint8_of_nat_mk(x_386);
x_388 = lean_unsigned_to_nat(0u);
x_389 = lean_int8_of_nat(x_388);
x_390 = lean_int8_dec_le(x_389, x_387);
if (x_390 == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_391 = lean_mk_string_unchecked("Neg", 3, 3);
x_392 = lean_mk_string_unchecked("neg", 3, 3);
x_393 = l_Lean_Name_mkStr2(x_391, x_392);
x_394 = l_Lean_Level_ofNat(x_388);
x_395 = lean_box(0);
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
x_397 = l_Lean_Expr_const___override(x_393, x_396);
lean_inc(x_203);
x_398 = l_Lean_Name_mkStr1(x_203);
x_399 = l_Lean_Expr_const___override(x_398, x_395);
x_400 = lean_mk_string_unchecked("instNeg", 7, 7);
x_401 = l_Lean_Name_mkStr2(x_203, x_400);
x_402 = l_Lean_Expr_const___override(x_401, x_395);
x_403 = lean_int8_to_int(x_387);
x_404 = lean_int_neg(x_403);
lean_dec(x_403);
x_405 = l_Int_toNat(x_404);
lean_dec(x_404);
x_406 = l_Lean_instToExprInt8_mkNat(x_405);
x_407 = l_Lean_mkApp3(x_397, x_399, x_402, x_406);
x_184 = x_407;
goto block_187;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_dec(x_203);
x_408 = lean_int8_to_int(x_387);
x_409 = l_Int_toNat(x_408);
lean_dec(x_408);
x_410 = l_Lean_instToExprInt8_mkNat(x_409);
x_184 = x_410;
goto block_187;
}
}
}
}
else
{
lean_object* x_411; lean_object* x_412; uint8_t x_413; 
lean_dec(x_194);
lean_dec(x_192);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_411 = lean_ctor_get(x_2, 0);
lean_inc(x_411);
x_412 = lean_unsigned_to_nat(16u);
x_413 = lean_nat_dec_eq(x_411, x_412);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_200);
lean_dec(x_171);
lean_dec(x_2);
x_414 = lean_mk_string_unchecked("Value for Int16 was not 16 bit but ", 35, 35);
x_415 = l_Lean_stringToMessageData(x_414);
lean_dec(x_414);
x_416 = l___private_Init_Data_Repr_0__Nat_reprFast(x_411);
x_417 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_417, 0, x_416);
x_418 = l_Lean_MessageData_ofFormat(x_417);
x_419 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_419, 0, x_415);
lean_ctor_set(x_419, 1, x_418);
x_420 = lean_mk_string_unchecked(" bit", 4, 4);
x_421 = l_Lean_stringToMessageData(x_420);
lean_dec(x_420);
x_422 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_422, 0, x_419);
lean_ctor_set(x_422, 1, x_421);
x_423 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(x_422, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_423;
}
else
{
lean_object* x_424; uint16_t x_425; lean_object* x_426; uint16_t x_427; uint8_t x_428; 
lean_dec(x_411);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_424 = lean_ctor_get(x_2, 1);
lean_inc(x_424);
lean_dec(x_2);
x_425 = lean_uint16_of_nat_mk(x_424);
x_426 = lean_unsigned_to_nat(0u);
x_427 = lean_int16_of_nat(x_426);
x_428 = lean_int16_dec_le(x_427, x_425);
if (x_428 == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_429 = lean_mk_string_unchecked("Neg", 3, 3);
x_430 = lean_mk_string_unchecked("neg", 3, 3);
x_431 = l_Lean_Name_mkStr2(x_429, x_430);
x_432 = l_Lean_Level_ofNat(x_426);
x_433 = lean_box(0);
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set(x_434, 1, x_433);
x_435 = l_Lean_Expr_const___override(x_431, x_434);
lean_inc(x_200);
x_436 = l_Lean_Name_mkStr1(x_200);
x_437 = l_Lean_Expr_const___override(x_436, x_433);
x_438 = lean_mk_string_unchecked("instNeg", 7, 7);
x_439 = l_Lean_Name_mkStr2(x_200, x_438);
x_440 = l_Lean_Expr_const___override(x_439, x_433);
x_441 = lean_int16_to_int(x_425);
x_442 = lean_int_neg(x_441);
lean_dec(x_441);
x_443 = l_Int_toNat(x_442);
lean_dec(x_442);
x_444 = l_Lean_instToExprInt16_mkNat(x_443);
x_445 = l_Lean_mkApp3(x_435, x_437, x_440, x_444);
x_180 = x_445;
goto block_183;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_200);
x_446 = lean_int16_to_int(x_425);
x_447 = l_Int_toNat(x_446);
lean_dec(x_446);
x_448 = l_Lean_instToExprInt16_mkNat(x_447);
x_180 = x_448;
goto block_183;
}
}
}
}
else
{
lean_object* x_449; lean_object* x_450; uint8_t x_451; 
lean_dec(x_194);
lean_dec(x_192);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_449 = lean_ctor_get(x_2, 0);
lean_inc(x_449);
x_450 = lean_unsigned_to_nat(32u);
x_451 = lean_nat_dec_eq(x_449, x_450);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
lean_dec(x_197);
lean_dec(x_171);
lean_dec(x_2);
x_452 = lean_mk_string_unchecked("Value for Int32 was not 32 bit but ", 35, 35);
x_453 = l_Lean_stringToMessageData(x_452);
lean_dec(x_452);
x_454 = l___private_Init_Data_Repr_0__Nat_reprFast(x_449);
x_455 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_455, 0, x_454);
x_456 = l_Lean_MessageData_ofFormat(x_455);
x_457 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_457, 0, x_453);
lean_ctor_set(x_457, 1, x_456);
x_458 = lean_mk_string_unchecked(" bit", 4, 4);
x_459 = l_Lean_stringToMessageData(x_458);
lean_dec(x_458);
x_460 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_460, 0, x_457);
lean_ctor_set(x_460, 1, x_459);
x_461 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(x_460, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_461;
}
else
{
lean_object* x_462; uint32_t x_463; lean_object* x_464; uint32_t x_465; uint8_t x_466; 
lean_dec(x_449);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_462 = lean_ctor_get(x_2, 1);
lean_inc(x_462);
lean_dec(x_2);
x_463 = lean_uint32_of_nat_mk(x_462);
x_464 = lean_unsigned_to_nat(0u);
x_465 = lean_int32_of_nat(x_464);
x_466 = lean_int32_dec_le(x_465, x_463);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_467 = lean_mk_string_unchecked("Neg", 3, 3);
x_468 = lean_mk_string_unchecked("neg", 3, 3);
x_469 = l_Lean_Name_mkStr2(x_467, x_468);
x_470 = l_Lean_Level_ofNat(x_464);
x_471 = lean_box(0);
x_472 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_471);
x_473 = l_Lean_Expr_const___override(x_469, x_472);
lean_inc(x_197);
x_474 = l_Lean_Name_mkStr1(x_197);
x_475 = l_Lean_Expr_const___override(x_474, x_471);
x_476 = lean_mk_string_unchecked("instNeg", 7, 7);
x_477 = l_Lean_Name_mkStr2(x_197, x_476);
x_478 = l_Lean_Expr_const___override(x_477, x_471);
x_479 = lean_int32_to_int(x_463);
x_480 = lean_int_neg(x_479);
lean_dec(x_479);
x_481 = l_Int_toNat(x_480);
lean_dec(x_480);
x_482 = l_Lean_instToExprInt32_mkNat(x_481);
x_483 = l_Lean_mkApp3(x_473, x_475, x_478, x_482);
x_176 = x_483;
goto block_179;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
lean_dec(x_197);
x_484 = lean_int32_to_int(x_463);
x_485 = l_Int_toNat(x_484);
lean_dec(x_484);
x_486 = l_Lean_instToExprInt32_mkNat(x_485);
x_176 = x_486;
goto block_179;
}
}
}
}
else
{
lean_object* x_487; lean_object* x_488; uint8_t x_489; 
lean_dec(x_194);
lean_dec(x_192);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_487 = lean_ctor_get(x_2, 0);
lean_inc(x_487);
x_488 = lean_unsigned_to_nat(64u);
x_489 = lean_nat_dec_eq(x_487, x_488);
if (x_489 == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
lean_dec(x_193);
lean_dec(x_171);
lean_dec(x_2);
x_490 = lean_mk_string_unchecked("Value for Int64 was not 64 bit but ", 35, 35);
x_491 = l_Lean_stringToMessageData(x_490);
lean_dec(x_490);
x_492 = l___private_Init_Data_Repr_0__Nat_reprFast(x_487);
x_493 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_493, 0, x_492);
x_494 = l_Lean_MessageData_ofFormat(x_493);
x_495 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_495, 0, x_491);
lean_ctor_set(x_495, 1, x_494);
x_496 = lean_mk_string_unchecked(" bit", 4, 4);
x_497 = l_Lean_stringToMessageData(x_496);
lean_dec(x_496);
x_498 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_498, 0, x_495);
lean_ctor_set(x_498, 1, x_497);
x_499 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(x_498, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_499;
}
else
{
lean_object* x_500; uint64_t x_501; lean_object* x_502; uint64_t x_503; uint8_t x_504; 
lean_dec(x_487);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_500 = lean_ctor_get(x_2, 1);
lean_inc(x_500);
lean_dec(x_2);
x_501 = lean_uint64_of_nat_mk(x_500);
x_502 = lean_unsigned_to_nat(0u);
x_503 = lean_int64_of_nat(x_502);
x_504 = lean_int64_dec_le(x_503, x_501);
if (x_504 == 0)
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_505 = lean_mk_string_unchecked("Neg", 3, 3);
x_506 = lean_mk_string_unchecked("neg", 3, 3);
x_507 = l_Lean_Name_mkStr2(x_505, x_506);
x_508 = l_Lean_Level_ofNat(x_502);
x_509 = lean_box(0);
x_510 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_510, 0, x_508);
lean_ctor_set(x_510, 1, x_509);
x_511 = l_Lean_Expr_const___override(x_507, x_510);
lean_inc(x_193);
x_512 = l_Lean_Name_mkStr1(x_193);
x_513 = l_Lean_Expr_const___override(x_512, x_509);
x_514 = lean_mk_string_unchecked("instNeg", 7, 7);
x_515 = l_Lean_Name_mkStr2(x_193, x_514);
x_516 = l_Lean_Expr_const___override(x_515, x_509);
x_517 = lean_int64_to_int_sint(x_501);
x_518 = lean_int_neg(x_517);
lean_dec(x_517);
x_519 = l_Int_toNat(x_518);
lean_dec(x_518);
x_520 = l_Lean_instToExprInt64_mkNat(x_519);
x_521 = l_Lean_mkApp3(x_511, x_513, x_516, x_520);
x_172 = x_521;
goto block_175;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_193);
x_522 = lean_int64_to_int_sint(x_501);
x_523 = l_Int_toNat(x_522);
lean_dec(x_522);
x_524 = l_Lean_instToExprInt64_mkNat(x_523);
x_172 = x_524;
goto block_175;
}
}
}
block_175:
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_13);
return x_174;
}
block_179:
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_171);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_13);
return x_178;
}
block_183:
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_171);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_13);
return x_182;
}
block_187:
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_171);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_13);
return x_186;
}
block_191:
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_171);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_13);
return x_190;
}
}
block_168:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
switch (lean_obj_tag(x_21)) {
case 0:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_14);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Expr_bvar___override(x_23);
x_25 = l_Lean_Expr_app___override(x_24, x_22);
x_26 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation___lam__0(x_2, x_1, x_25, x_15, x_16, x_17, x_18, x_19, x_20, x_13);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_25);
return x_26;
}
case 1:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_14);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
x_29 = l_Lean_Expr_fvar___override(x_28);
x_30 = l_Lean_Expr_app___override(x_29, x_27);
x_31 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation___lam__0(x_2, x_1, x_30, x_15, x_16, x_17, x_18, x_19, x_20, x_13);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_30);
return x_31;
}
case 2:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_14);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_21, 0);
lean_inc(x_33);
lean_dec(x_21);
x_34 = l_Lean_Expr_mvar___override(x_33);
x_35 = l_Lean_Expr_app___override(x_34, x_32);
x_36 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation___lam__0(x_2, x_1, x_35, x_15, x_16, x_17, x_18, x_19, x_20, x_13);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_35);
return x_36;
}
case 3:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_14);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_21, 0);
lean_inc(x_38);
lean_dec(x_21);
x_39 = l_Lean_Expr_sort___override(x_38);
x_40 = l_Lean_Expr_app___override(x_39, x_37);
x_41 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation___lam__0(x_2, x_1, x_40, x_15, x_16, x_17, x_18, x_19, x_20, x_13);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_40);
return x_41;
}
case 4:
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_21, 0);
lean_inc(x_42);
switch (lean_obj_tag(x_42)) {
case 0:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_14);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_21, 1);
lean_inc(x_44);
lean_dec(x_21);
x_45 = lean_box(0);
x_46 = l_Lean_Expr_const___override(x_45, x_44);
x_47 = l_Lean_Expr_app___override(x_46, x_43);
x_48 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation___lam__0(x_2, x_1, x_47, x_15, x_16, x_17, x_18, x_19, x_20, x_13);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_47);
return x_48;
}
case 1:
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
lean_dec(x_21);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_dec(x_42);
x_53 = lean_mk_string_unchecked("enumToBitVec", 12, 12);
x_54 = lean_string_dec_eq(x_52, x_53);
lean_dec(x_53);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_55 = lean_ctor_get(x_2, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
lean_dec(x_2);
x_57 = lean_mk_string_unchecked("BitVec", 6, 6);
x_58 = lean_mk_string_unchecked("ofNat", 5, 5);
x_59 = l_Lean_Name_mkStr2(x_57, x_58);
x_60 = l_Lean_Expr_const___override(x_59, x_49);
lean_inc(x_55);
x_61 = l_Lean_mkNatLit(x_55);
x_62 = l_BitVec_toNat(x_55, x_56);
lean_dec(x_56);
lean_dec(x_55);
x_63 = l_Lean_mkNatLit(x_62);
x_64 = l_Lean_mkAppB(x_60, x_61, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_64);
if (lean_is_scalar(x_14)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_14;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_13);
return x_66;
}
else
{
lean_object* x_67; 
lean_dec(x_14);
lean_dec(x_1);
x_67 = l_Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0(x_51, x_15, x_16, x_17, x_18, x_19, x_20, x_13);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 5)
{
uint8_t x_69; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_69 = !lean_is_exclusive(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_70 = lean_ctor_get(x_67, 0);
lean_dec(x_70);
x_71 = lean_ctor_get(x_68, 0);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_ctor_get(x_71, 4);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_box(0);
x_74 = lean_ctor_get(x_2, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_2, 1);
lean_inc(x_75);
lean_dec(x_2);
x_76 = l_BitVec_toNat(x_74, x_75);
lean_dec(x_75);
lean_dec(x_74);
x_77 = l___private_Init_GetElem_0__List_get_x21Internal___redArg(x_73, x_72, x_76);
lean_dec(x_72);
x_78 = l_Lean_Expr_const___override(x_77, x_49);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_50);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_67, 0, x_79);
return x_67;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_80 = lean_ctor_get(x_67, 1);
lean_inc(x_80);
lean_dec(x_67);
x_81 = lean_ctor_get(x_68, 0);
lean_inc(x_81);
lean_dec(x_68);
x_82 = lean_ctor_get(x_81, 4);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = lean_ctor_get(x_2, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_2, 1);
lean_inc(x_85);
lean_dec(x_2);
x_86 = l_BitVec_toNat(x_84, x_85);
lean_dec(x_85);
lean_dec(x_84);
x_87 = l___private_Init_GetElem_0__List_get_x21Internal___redArg(x_83, x_82, x_86);
lean_dec(x_82);
x_88 = l_Lean_Expr_const___override(x_87, x_49);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_50);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_80);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_68);
lean_dec(x_50);
lean_dec(x_2);
x_91 = lean_ctor_get(x_67, 1);
lean_inc(x_91);
lean_dec(x_67);
x_92 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.BVDecide", 43, 43);
x_93 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.DiagnosisM.diagnose.transformEquation", 72, 72);
x_94 = lean_unsigned_to_nat(230u);
x_95 = lean_unsigned_to_nat(61u);
x_96 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_97 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_92, x_93, x_94, x_95, x_96);
lean_dec(x_96);
lean_dec(x_93);
lean_dec(x_92);
x_98 = l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__2(x_97, x_15, x_16, x_17, x_18, x_19, x_20, x_91);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_50);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_67);
if (x_99 == 0)
{
return x_67;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_67, 0);
x_101 = lean_ctor_get(x_67, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_67);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_14);
x_103 = lean_ctor_get(x_1, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_42, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_42, 1);
lean_inc(x_105);
lean_dec(x_42);
x_106 = l_Lean_Name_str___override(x_104, x_105);
x_107 = l_Lean_Expr_const___override(x_106, x_49);
x_108 = l_Lean_Expr_app___override(x_107, x_103);
x_109 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation___lam__0(x_2, x_1, x_108, x_15, x_16, x_17, x_18, x_19, x_20, x_13);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_108);
return x_109;
}
}
default: 
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_14);
x_110 = lean_ctor_get(x_1, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_21, 1);
lean_inc(x_111);
lean_dec(x_21);
x_112 = lean_ctor_get(x_42, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_42, 1);
lean_inc(x_113);
lean_dec(x_42);
x_114 = l_Lean_Name_num___override(x_112, x_113);
x_115 = l_Lean_Expr_const___override(x_114, x_111);
x_116 = l_Lean_Expr_app___override(x_115, x_110);
x_117 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation___lam__0(x_2, x_1, x_116, x_15, x_16, x_17, x_18, x_19, x_20, x_13);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_116);
return x_117;
}
}
}
case 5:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_14);
x_118 = lean_ctor_get(x_1, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_21, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_21, 1);
lean_inc(x_120);
lean_dec(x_21);
x_121 = l_Lean_Expr_app___override(x_119, x_120);
x_122 = l_Lean_Expr_app___override(x_121, x_118);
x_123 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation___lam__0(x_2, x_1, x_122, x_15, x_16, x_17, x_18, x_19, x_20, x_13);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_122);
return x_123;
}
case 6:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_14);
x_124 = lean_ctor_get(x_1, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_21, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_21, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_21, 2);
lean_inc(x_127);
x_128 = lean_ctor_get_uint8(x_21, sizeof(void*)*3 + 8);
lean_dec(x_21);
x_129 = l_Lean_Expr_lam___override(x_125, x_126, x_127, x_128);
x_130 = l_Lean_Expr_app___override(x_129, x_124);
x_131 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation___lam__0(x_2, x_1, x_130, x_15, x_16, x_17, x_18, x_19, x_20, x_13);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_130);
return x_131;
}
case 7:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_14);
x_132 = lean_ctor_get(x_1, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_21, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_21, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_21, 2);
lean_inc(x_135);
x_136 = lean_ctor_get_uint8(x_21, sizeof(void*)*3 + 8);
lean_dec(x_21);
x_137 = l_Lean_Expr_forallE___override(x_133, x_134, x_135, x_136);
x_138 = l_Lean_Expr_app___override(x_137, x_132);
x_139 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation___lam__0(x_2, x_1, x_138, x_15, x_16, x_17, x_18, x_19, x_20, x_13);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_138);
return x_139;
}
case 8:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_14);
x_140 = lean_ctor_get(x_1, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_21, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_21, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_21, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_21, 3);
lean_inc(x_144);
x_145 = lean_ctor_get_uint8(x_21, sizeof(void*)*4 + 8);
lean_dec(x_21);
x_146 = l_Lean_Expr_letE___override(x_141, x_142, x_143, x_144, x_145);
x_147 = l_Lean_Expr_app___override(x_146, x_140);
x_148 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation___lam__0(x_2, x_1, x_147, x_15, x_16, x_17, x_18, x_19, x_20, x_13);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_147);
return x_148;
}
case 9:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_14);
x_149 = lean_ctor_get(x_1, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_21, 0);
lean_inc(x_150);
lean_dec(x_21);
x_151 = l_Lean_Expr_lit___override(x_150);
x_152 = l_Lean_Expr_app___override(x_151, x_149);
x_153 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation___lam__0(x_2, x_1, x_152, x_15, x_16, x_17, x_18, x_19, x_20, x_13);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_152);
return x_153;
}
case 10:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_14);
x_154 = lean_ctor_get(x_1, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_21, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_21, 1);
lean_inc(x_156);
lean_dec(x_21);
x_157 = l_Lean_Expr_mdata___override(x_155, x_156);
x_158 = l_Lean_Expr_app___override(x_157, x_154);
x_159 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation___lam__0(x_2, x_1, x_158, x_15, x_16, x_17, x_18, x_19, x_20, x_13);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_158);
return x_159;
}
default: 
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_14);
x_160 = lean_ctor_get(x_1, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_21, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_21, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_21, 2);
lean_inc(x_163);
lean_dec(x_21);
x_164 = l_Lean_Expr_proj___override(x_161, x_162, x_163);
x_165 = l_Lean_Expr_app___override(x_164, x_160);
x_166 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation___lam__0(x_2, x_1, x_165, x_15, x_16, x_17, x_18, x_19, x_20, x_13);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_165);
return x_166;
}
}
}
else
{
lean_object* x_167; 
lean_dec(x_14);
lean_inc(x_1);
x_167 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation___lam__0(x_2, x_1, x_1, x_15, x_16, x_17, x_18, x_19, x_20, x_13);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_1);
return x_167;
}
}
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_525 = lean_ctor_get(x_2, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_2, 1);
lean_inc(x_526);
lean_dec(x_2);
x_527 = lean_mk_string_unchecked("BitVec", 6, 6);
x_528 = lean_mk_string_unchecked("ofNat", 5, 5);
x_529 = l_Lean_Name_mkStr2(x_527, x_528);
x_530 = lean_box(0);
x_531 = l_Lean_Expr_const___override(x_529, x_530);
lean_inc(x_525);
x_532 = l_Lean_mkNatLit(x_525);
x_533 = l_BitVec_toNat(x_525, x_526);
lean_dec(x_526);
lean_dec(x_525);
x_534 = l_Lean_mkNatLit(x_533);
x_535 = l_Lean_mkAppB(x_531, x_532, x_534);
x_536 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_536, 0, x_1);
lean_ctor_set(x_536, 1, x_535);
x_537 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_537, 0, x_536);
lean_ctor_set(x_537, 1, x_9);
return x_537;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getConstInfo___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation_spec__2___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_3, x_2);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_4);
x_21 = lean_array_uget(x_1, x_3);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_transformEquation(x_22, x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_st_ref_take(x_6, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 2);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_array_push(x_33, x_25);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_st_ref_set(x_6, x_35, x_30);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_box(0);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_27, 0);
lean_inc(x_39);
lean_dec(x_27);
lean_inc(x_7);
x_40 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_checkRelevantHypsUsed(x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_12 = x_38;
x_13 = x_41;
goto block_18;
}
else
{
uint8_t x_42; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_40);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint64_t x_60; lean_object* x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; lean_object* x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; size_t x_69; size_t x_70; lean_object* x_71; size_t x_72; size_t x_73; size_t x_74; lean_object* x_75; uint8_t x_76; 
x_46 = lean_st_ref_take(x_6, x_37);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_56 = lean_ctor_get(x_47, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
x_59 = lean_array_get_size(x_58);
x_60 = l_Lean_Expr_hash(x_27);
x_61 = lean_unsigned_to_nat(32u);
x_62 = lean_uint64_of_nat(x_61);
x_63 = lean_uint64_shift_right(x_60, x_62);
x_64 = lean_uint64_xor(x_60, x_63);
x_65 = lean_unsigned_to_nat(16u);
x_66 = lean_uint64_of_nat(x_65);
x_67 = lean_uint64_shift_right(x_64, x_66);
x_68 = lean_uint64_xor(x_64, x_67);
x_69 = lean_uint64_to_usize(x_68);
x_70 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_usize_of_nat(x_71);
x_73 = lean_usize_sub(x_70, x_72);
x_74 = lean_usize_land(x_69, x_73);
x_75 = lean_array_uget(x_58, x_74);
x_76 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0(lean_box(0), x_27, x_75);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_56);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_78 = lean_ctor_get(x_56, 1);
lean_dec(x_78);
x_79 = lean_ctor_get(x_56, 0);
lean_dec(x_79);
x_80 = lean_nat_add(x_57, x_71);
lean_dec(x_57);
x_81 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_81, 0, x_27);
lean_ctor_set(x_81, 1, x_38);
lean_ctor_set(x_81, 2, x_75);
x_82 = lean_array_uset(x_58, x_74, x_81);
x_83 = lean_unsigned_to_nat(2u);
x_84 = lean_nat_shiftl(x_80, x_83);
x_85 = lean_unsigned_to_nat(3u);
x_86 = lean_nat_div(x_84, x_85);
lean_dec(x_84);
x_87 = lean_array_get_size(x_82);
x_88 = lean_nat_dec_le(x_86, x_87);
lean_dec(x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(x_82);
lean_ctor_set(x_56, 1, x_89);
lean_ctor_set(x_56, 0, x_80);
x_49 = x_56;
goto block_55;
}
else
{
lean_ctor_set(x_56, 1, x_82);
lean_ctor_set(x_56, 0, x_80);
x_49 = x_56;
goto block_55;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
lean_dec(x_56);
x_90 = lean_nat_add(x_57, x_71);
lean_dec(x_57);
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_27);
lean_ctor_set(x_91, 1, x_38);
lean_ctor_set(x_91, 2, x_75);
x_92 = lean_array_uset(x_58, x_74, x_91);
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
lean_object* x_99; lean_object* x_100; 
x_99 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(x_92);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_90);
lean_ctor_set(x_100, 1, x_99);
x_49 = x_100;
goto block_55;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_90);
lean_ctor_set(x_101, 1, x_92);
x_49 = x_101;
goto block_55;
}
}
}
else
{
lean_dec(x_75);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_27);
x_49 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 2);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set(x_52, 2, x_51);
x_53 = lean_st_ref_set(x_6, x_52, x_48);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_12 = x_38;
x_13 = x_54;
goto block_18;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_102 = !lean_is_exclusive(x_24);
if (x_102 == 0)
{
return x_24;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_24, 0);
x_104 = lean_ctor_get(x_24, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_24);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
block_18:
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_4 = x_12;
x_11 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; size_t x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = lean_array_size(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_usize_of_nat(x_11);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_spec__0(x_8, x_10, x_12, x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_9);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_uninterpretedExplainer_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_uninterpretedExplainer_spec__0(x_1, x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_uninterpretedExplainer_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_sub(x_2, x_7);
x_9 = lean_array_uget(x_1, x_8);
x_10 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_uninterpretedExplainer_spec__0(x_4, x_9);
lean_dec(x_9);
lean_dec(x_4);
x_2 = x_8;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_uninterpretedExplainer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_box(0);
x_19 = lean_ctor_get(x_14, 1);
x_20 = lean_array_get_size(x_19);
x_21 = lean_nat_dec_lt(x_16, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
x_2 = x_18;
goto block_13;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_23 = lean_usize_of_nat(x_16);
x_24 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_uninterpretedExplainer_spec__1(x_19, x_22, x_23, x_18);
x_2 = x_24;
goto block_13;
}
}
else
{
lean_object* x_25; 
x_25 = lean_box(0);
return x_25;
}
block_13:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_mk_string_unchecked("It abstracted the following unsupported expressions as opaque variables: ", 73, 73);
x_4 = l_Lean_stringToMessageData(x_3);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_2, x_5);
x_7 = l_Lean_MessageData_ofList(x_6);
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_mk_string_unchecked("", 0, 0);
x_10 = l_Lean_stringToMessageData(x_9);
lean_dec(x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_uninterpretedExplainer_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_uninterpretedExplainer_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_uninterpretedExplainer_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_uninterpretedExplainer_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_uninterpretedExplainer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_uninterpretedExplainer(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer_spec__0(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Expr_fvar___override(x_5);
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
x_11 = l_Lean_Expr_fvar___override(x_9);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer_spec__1(x_1, x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_sub(x_2, x_7);
x_9 = lean_array_uget(x_1, x_8);
x_10 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer_spec__1(x_4, x_9);
lean_dec(x_9);
lean_dec(x_4);
x_2 = x_8;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_16, 0);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_box(0);
x_21 = lean_ctor_get(x_16, 1);
x_22 = lean_array_get_size(x_21);
x_23 = lean_nat_dec_lt(x_18, x_22);
if (x_23 == 0)
{
lean_dec(x_22);
x_2 = x_20;
goto block_15;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_25 = lean_usize_of_nat(x_18);
x_26 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer_spec__2(x_21, x_24, x_25, x_20);
x_2 = x_26;
goto block_15;
}
}
else
{
lean_object* x_27; 
x_27 = lean_box(0);
return x_27;
}
block_15:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer_spec__0(x_2, x_3);
x_5 = lean_mk_string_unchecked("The following potentially relevant hypotheses could not be used: ", 65, 65);
x_6 = l_Lean_stringToMessageData(x_5);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_4, x_7);
x_9 = l_Lean_MessageData_ofList(x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_mk_string_unchecked("", 0, 0);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer_spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_explainers() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_uninterpretedExplainer___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_unusedRelevantHypothesesExplainer___boxed), 1, 0);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Elab_Tactic_BVDecide_Frontend_explainCounterExampleQuality_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = lean_apply_1(x_4, x_1);
if (lean_obj_tag(x_6) == 0)
{
x_3 = x_5;
goto _start;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_array_push(x_2, x_8);
x_2 = x_9;
x_3 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_explainCounterExampleQuality_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_mk_string_unchecked("", 0, 0);
x_11 = l_Lean_stringToMessageData(x_10);
lean_dec(x_10);
x_12 = l_Lean_MessageData_ofExpr(x_8);
lean_ctor_set_tag(x_6, 7);
lean_ctor_set(x_6, 1, x_12);
lean_ctor_set(x_6, 0, x_11);
x_13 = lean_mk_string_unchecked(" = ", 3, 3);
x_14 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_MessageData_ofExpr(x_9);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_mk_string_unchecked("\n", 1, 1);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_usize_of_nat(x_22);
x_24 = lean_usize_add(x_2, x_23);
x_2 = x_24;
x_4 = x_21;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; 
x_26 = lean_ctor_get(x_6, 0);
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_6);
x_28 = lean_mk_string_unchecked("", 0, 0);
x_29 = l_Lean_stringToMessageData(x_28);
lean_dec(x_28);
x_30 = l_Lean_MessageData_ofExpr(x_26);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_mk_string_unchecked(" = ", 3, 3);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_MessageData_ofExpr(x_27);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_mk_string_unchecked("\n", 1, 1);
x_38 = l_Lean_stringToMessageData(x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_usize_of_nat(x_41);
x_43 = lean_usize_add(x_2, x_42);
x_2 = x_43;
x_4 = x_40;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_explainCounterExampleQuality_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_mk_string_unchecked("- ", 2, 2);
x_8 = l_Lean_stringToMessageData(x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_mk_string_unchecked("\n", 1, 1);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_13;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_explainCounterExampleQuality(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_diagnose), 7, 0);
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_DiagnosisM_run(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
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
x_12 = lean_unsigned_to_nat(0u);
x_25 = lean_mk_empty_array_with_capacity(x_12);
x_26 = l_Lean_Elab_Tactic_BVDecide_Frontend_explainers;
lean_inc(x_9);
x_27 = l_List_foldl___at___Lean_Elab_Tactic_BVDecide_Frontend_explainCounterExampleQuality_spec__0(x_9, x_25, x_26);
x_28 = lean_mk_string_unchecked("", 0, 0);
x_29 = l_Lean_stringToMessageData(x_28);
lean_dec(x_28);
x_30 = l_Array_isEmpty___redArg(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_40; uint8_t x_41; 
x_31 = lean_mk_string_unchecked("The prover found a potentially spurious counterexample:\n", 56, 56);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
lean_inc(x_29);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
x_40 = lean_array_get_size(x_27);
x_41 = lean_nat_dec_lt(x_12, x_40);
if (x_41 == 0)
{
lean_dec(x_40);
lean_dec(x_27);
x_34 = x_29;
goto block_39;
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_40, x_40);
if (x_42 == 0)
{
lean_dec(x_40);
lean_dec(x_27);
x_34 = x_29;
goto block_39;
}
else
{
size_t x_43; size_t x_44; lean_object* x_45; 
x_43 = lean_usize_of_nat(x_12);
x_44 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_45 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_explainCounterExampleQuality_spec__2(x_27, x_43, x_44, x_29);
lean_dec(x_27);
x_34 = x_45;
goto block_39;
}
}
block_39:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_mk_string_unchecked("Consider the following assignment:\n", 35, 35);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_13 = x_38;
goto block_24;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_27);
x_46 = lean_mk_string_unchecked("The prover found a counterexample, consider the following assignment:\n", 70, 70);
x_47 = l_Lean_stringToMessageData(x_46);
lean_dec(x_46);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_29);
lean_ctor_set(x_48, 1, x_47);
x_13 = x_48;
goto block_24;
}
block_24:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_9, 2);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_array_get_size(x_14);
x_16 = lean_nat_dec_lt(x_12, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_14);
if (lean_is_scalar(x_11)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_11;
}
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_15, x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_14);
if (lean_is_scalar(x_11)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_11;
}
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_usize_of_nat(x_12);
x_21 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_22 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_explainCounterExampleQuality_spec__1(x_14, x_20, x_21, x_13);
lean_dec(x_14);
if (lean_is_scalar(x_11)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_11;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_8);
if (x_49 == 0)
{
return x_8;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_8, 0);
x_51 = lean_ctor_get(x_8, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_8);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_explainCounterExampleQuality_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_explainCounterExampleQuality_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_explainCounterExampleQuality_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_explainCounterExampleQuality_spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_explainCounterExampleQuality___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_explainCounterExampleQuality(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof_mkAuxDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_box(0);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_3);
x_9 = lean_box(1);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_7);
x_12 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_11);
x_13 = lean_unbox(x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*4, x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = l_Lean_addAndCompile(x_14, x_4, x_5, x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_mk_string_unchecked("Compiling expr term", 19, 19);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_MessageData_ofFormat(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof_mkAuxDecl(x_1, x_2, x_3, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_mk_string_unchecked("Compiling proof certificate term", 32, 32);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_MessageData_ofFormat(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_mk_string_unchecked("Compiling reflection proof term", 31, 31);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_MessageData_ofFormat(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof_mkAuxDecl(x_1, x_2, x_3, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_mk_string_unchecked("Verifying LRAT certificate", 26, 26);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_MessageData_ofFormat(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__6(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_11, 3);
x_17 = l_Lean_maxRecDepth;
x_18 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_1, x_17);
x_19 = lean_ctor_get(x_11, 5);
x_20 = lean_ctor_get(x_11, 6);
x_21 = lean_ctor_get(x_11, 7);
x_22 = lean_ctor_get(x_11, 8);
x_23 = lean_ctor_get(x_11, 9);
x_24 = lean_ctor_get(x_11, 10);
x_25 = lean_ctor_get(x_11, 11);
x_26 = lean_ctor_get_uint8(x_11, sizeof(void*)*13 + 1);
x_27 = lean_ctor_get(x_11, 12);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_28 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_15);
lean_ctor_set(x_28, 2, x_1);
lean_ctor_set(x_28, 3, x_16);
lean_ctor_set(x_28, 4, x_18);
lean_ctor_set(x_28, 5, x_19);
lean_ctor_set(x_28, 6, x_20);
lean_ctor_set(x_28, 7, x_21);
lean_ctor_set(x_28, 8, x_22);
lean_ctor_set(x_28, 9, x_23);
lean_ctor_set(x_28, 10, x_24);
lean_ctor_set(x_28, 11, x_25);
lean_ctor_set(x_28, 12, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*13, x_2);
lean_ctor_set_uint8(x_28, sizeof(void*)*13 + 1, x_26);
x_29 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_28, x_12, x_13);
return x_29;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_37; lean_object* x_38; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__0___boxed), 6, 0);
x_10 = lean_mk_string_unchecked("Meta", 4, 4);
x_11 = lean_mk_string_unchecked("Tactic", 6, 6);
x_12 = lean_mk_string_unchecked("sat", 3, 3);
lean_inc(x_11);
x_13 = l_Lean_Name_mkStr3(x_10, x_11, x_12);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 3);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_mk_string_unchecked("Std", 3, 3);
x_17 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_18 = lean_mk_string_unchecked("BVLogicalExpr", 13, 13);
lean_inc(x_17);
lean_inc(x_11);
lean_inc(x_16);
x_19 = l_Lean_Name_mkStr4(x_16, x_11, x_17, x_18);
x_20 = lean_box(0);
x_21 = l_Lean_Expr_const___override(x_19, x_20);
lean_inc(x_14);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__1___boxed), 8, 3);
lean_closure_set(x_22, 0, x_14);
lean_closure_set(x_22, 1, x_15);
lean_closure_set(x_22, 2, x_21);
x_23 = lean_box(1);
x_24 = lean_mk_string_unchecked("", 0, 0);
x_37 = lean_unbox(x_23);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_24);
lean_inc(x_13);
x_38 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_13, x_9, x_22, x_37, x_24, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__2___boxed), 6, 0);
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
x_42 = l_Lean_mkStrLit(x_1);
x_43 = lean_mk_string_unchecked("String", 6, 6);
x_44 = l_Lean_Name_mkStr1(x_43);
x_45 = l_Lean_Expr_const___override(x_44, x_20);
lean_inc(x_41);
x_46 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__1___boxed), 8, 3);
lean_closure_set(x_46, 0, x_41);
lean_closure_set(x_46, 1, x_42);
lean_closure_set(x_46, 2, x_45);
x_47 = lean_unbox(x_23);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_24);
lean_inc(x_13);
x_48 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_13, x_40, x_46, x_47, x_24, x_4, x_5, x_6, x_7, x_39);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__4___boxed), 6, 0);
x_51 = l_Lean_Expr_const___override(x_14, x_20);
x_52 = l_Lean_Expr_const___override(x_41, x_20);
x_53 = lean_mk_string_unchecked("Reflect", 7, 7);
x_75 = lean_mk_string_unchecked("verifyBVExpr", 12, 12);
lean_inc(x_53);
lean_inc(x_17);
lean_inc(x_11);
lean_inc(x_16);
x_76 = l_Lean_Name_mkStr5(x_16, x_11, x_17, x_53, x_75);
x_77 = l_Lean_Expr_const___override(x_76, x_20);
lean_inc(x_52);
lean_inc(x_51);
x_78 = l_Lean_mkAppB(x_77, x_51, x_52);
x_79 = lean_ctor_get(x_2, 2);
lean_inc(x_79);
lean_dec(x_2);
x_80 = lean_mk_string_unchecked("Bool", 4, 4);
lean_inc(x_80);
x_81 = l_Lean_Name_mkStr1(x_80);
x_82 = l_Lean_Expr_const___override(x_81, x_20);
lean_inc(x_79);
x_83 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__3___boxed), 8, 3);
lean_closure_set(x_83, 0, x_79);
lean_closure_set(x_83, 1, x_78);
lean_closure_set(x_83, 2, x_82);
x_84 = lean_unbox(x_23);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_24);
lean_inc(x_13);
x_85 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_13, x_50, x_83, x_84, x_24, x_4, x_5, x_6, x_7, x_49);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = l_Lean_Expr_const___override(x_79, x_20);
x_88 = lean_mk_string_unchecked("true", 4, 4);
x_89 = l_Lean_Name_mkStr2(x_80, x_88);
x_90 = l_Lean_Expr_const___override(x_89, x_20);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_90);
lean_inc(x_87);
x_91 = l_Lean_Meta_mkEq(x_87, x_90, x_4, x_5, x_6, x_7, x_86);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_90);
x_94 = l_Lean_Meta_mkEqRefl(x_90, x_4, x_5, x_6, x_7, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; uint8_t x_115; lean_object* x_160; uint8_t x_161; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_mk_string_unchecked("Lean", 4, 4);
x_98 = lean_mk_string_unchecked("ofReduceBool", 12, 12);
x_99 = l_Lean_Name_mkStr2(x_97, x_98);
x_100 = lean_st_ref_get(x_7, x_96);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l_Lean_Expr_const___override(x_99, x_20);
x_104 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__5___boxed), 6, 0);
x_105 = l_Lean_mkApp3(x_103, x_87, x_90, x_95);
x_106 = lean_box(0);
x_107 = lean_box(0);
x_108 = lean_ctor_get(x_6, 2);
lean_inc(x_108);
x_109 = l_Lean_Elab_async;
x_110 = lean_box(0);
x_111 = l_Lean_diagnostics;
x_112 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___boxed), 10, 5);
lean_closure_set(x_112, 0, x_106);
lean_closure_set(x_112, 1, x_92);
lean_closure_set(x_112, 2, x_105);
lean_closure_set(x_112, 3, x_107);
lean_closure_set(x_112, 4, x_23);
x_113 = lean_unbox(x_110);
x_114 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_108, x_109, x_113);
x_115 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_114, x_111);
x_160 = lean_ctor_get(x_101, 0);
lean_inc(x_160);
lean_dec(x_101);
x_161 = l_Lean_Kernel_isDiagnosticsEnabled(x_160);
lean_dec(x_160);
if (x_161 == 0)
{
if (x_115 == 0)
{
goto block_119;
}
else
{
goto block_159;
}
}
else
{
if (x_115 == 0)
{
goto block_159;
}
else
{
goto block_119;
}
}
block_119:
{
lean_object* x_116; uint8_t x_117; lean_object* x_118; 
x_116 = lean_box(0);
x_117 = lean_unbox(x_23);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_24);
x_118 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__6(x_114, x_115, x_13, x_104, x_112, x_117, x_24, x_4, x_5, x_116, x_6, x_7, x_102);
x_54 = x_118;
goto block_74;
}
block_159:
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_st_ref_take(x_7, x_102);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; 
x_122 = lean_ctor_get(x_120, 0);
x_123 = lean_ctor_get(x_120, 1);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
x_125 = l_Lean_Kernel_enableDiag(x_124, x_115);
x_126 = lean_ctor_get(x_122, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_122, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_122, 3);
lean_inc(x_128);
x_129 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_129);
lean_inc(x_130);
lean_ctor_set(x_120, 1, x_130);
lean_ctor_set(x_120, 0, x_130);
x_131 = lean_ctor_get(x_122, 5);
lean_inc(x_131);
x_132 = lean_ctor_get(x_122, 6);
lean_inc(x_132);
x_133 = lean_ctor_get(x_122, 7);
lean_inc(x_133);
lean_dec(x_122);
x_134 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_126);
lean_ctor_set(x_134, 2, x_127);
lean_ctor_set(x_134, 3, x_128);
lean_ctor_set(x_134, 4, x_120);
lean_ctor_set(x_134, 5, x_131);
lean_ctor_set(x_134, 6, x_132);
lean_ctor_set(x_134, 7, x_133);
x_135 = lean_st_ref_set(x_7, x_134, x_123);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_137 = lean_box(0);
x_138 = lean_unbox(x_23);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_24);
x_139 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__6(x_114, x_115, x_13, x_104, x_112, x_138, x_24, x_4, x_5, x_137, x_6, x_7, x_136);
x_54 = x_139;
goto block_74;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; 
x_140 = lean_ctor_get(x_120, 0);
x_141 = lean_ctor_get(x_120, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_120);
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
x_143 = l_Lean_Kernel_enableDiag(x_142, x_115);
x_144 = lean_ctor_get(x_140, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_140, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_140, 3);
lean_inc(x_146);
x_147 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_147);
lean_inc(x_148);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_ctor_get(x_140, 5);
lean_inc(x_150);
x_151 = lean_ctor_get(x_140, 6);
lean_inc(x_151);
x_152 = lean_ctor_get(x_140, 7);
lean_inc(x_152);
lean_dec(x_140);
x_153 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_153, 0, x_143);
lean_ctor_set(x_153, 1, x_144);
lean_ctor_set(x_153, 2, x_145);
lean_ctor_set(x_153, 3, x_146);
lean_ctor_set(x_153, 4, x_149);
lean_ctor_set(x_153, 5, x_150);
lean_ctor_set(x_153, 6, x_151);
lean_ctor_set(x_153, 7, x_152);
x_154 = lean_st_ref_set(x_7, x_153, x_141);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_box(0);
x_157 = lean_unbox(x_23);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_24);
x_158 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__6(x_114, x_115, x_13, x_104, x_112, x_157, x_24, x_4, x_5, x_156, x_6, x_7, x_155);
x_54 = x_158;
goto block_74;
}
}
}
else
{
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_94;
}
}
else
{
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_91;
}
}
else
{
uint8_t x_162; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_162 = !lean_is_exclusive(x_85);
if (x_162 == 0)
{
return x_85;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_85, 0);
x_164 = lean_ctor_get(x_85, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_85);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
block_74:
{
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_mk_string_unchecked("unsat_of_verifyBVExpr_eq_true", 29, 29);
x_58 = l_Lean_Name_mkStr5(x_16, x_11, x_17, x_53, x_57);
x_59 = l_Lean_Expr_const___override(x_58, x_20);
x_60 = l_Lean_Expr_const___override(x_56, x_20);
x_61 = l_Lean_mkApp3(x_59, x_51, x_52, x_60);
lean_ctor_set(x_54, 0, x_61);
return x_54;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_54, 0);
x_63 = lean_ctor_get(x_54, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_54);
x_64 = lean_mk_string_unchecked("unsat_of_verifyBVExpr_eq_true", 29, 29);
x_65 = l_Lean_Name_mkStr5(x_16, x_11, x_17, x_53, x_64);
x_66 = l_Lean_Expr_const___override(x_65, x_20);
x_67 = l_Lean_Expr_const___override(x_62, x_20);
x_68 = l_Lean_mkApp3(x_66, x_51, x_52, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_63);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
x_70 = lean_ctor_get(x_54, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_54, 1);
lean_inc(x_71);
lean_dec(x_54);
x_72 = l_Lean_Exception_isInterrupt(x_70);
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = l_Lean_Exception_isRuntime(x_70);
x_25 = x_70;
x_26 = x_71;
x_27 = x_73;
goto block_36;
}
else
{
x_25 = x_70;
x_26 = x_71;
x_27 = x_72;
goto block_36;
}
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_41);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_166 = !lean_is_exclusive(x_48);
if (x_166 == 0)
{
return x_48;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_48, 0);
x_168 = lean_ctor_get(x_48, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_48);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_170 = !lean_is_exclusive(x_38);
if (x_170 == 0)
{
return x_38;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_38, 0);
x_172 = lean_ctor_get(x_38, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_38);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
block_36:
{
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_mk_string_unchecked("Failed to check the LRAT certificate in the kernel:\n", 52, 52);
x_29 = l_Lean_stringToMessageData(x_28);
lean_dec(x_28);
x_30 = l_Lean_Exception_toMessageData(x_25);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_33, x_4, x_5, x_6, x_7, x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_34;
}
else
{
lean_object* x_35; 
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_26);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___lam__6(x_1, x_14, x_3, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_11);
lean_dec(x_10);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Std_Sat_AIG_relabelNat_x27___at___Std_Sat_AIG_relabelNat___at___Std_Sat_AIG_Entrypoint_relabelNat___at___Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__0(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_dec_eq(x_5, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__1___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_uint64_of_nat(x_4);
x_8 = lean_unsigned_to_nat(32u);
x_9 = lean_uint64_of_nat(x_8);
x_10 = lean_uint64_shift_right(x_7, x_9);
x_11 = lean_uint64_xor(x_7, x_10);
x_12 = lean_unsigned_to_nat(16u);
x_13 = lean_uint64_of_nat(x_12);
x_14 = lean_uint64_shift_right(x_11, x_13);
x_15 = lean_uint64_xor(x_11, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_sub(x_17, x_19);
x_21 = lean_usize_land(x_16, x_20);
x_22 = lean_array_uget(x_1, x_21);
lean_ctor_set(x_2, 2, x_22);
x_23 = lean_array_uset(x_1, x_21, x_2);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; size_t x_38; size_t x_39; lean_object* x_40; size_t x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_28 = lean_array_get_size(x_1);
x_29 = lean_uint64_of_nat(x_25);
x_30 = lean_unsigned_to_nat(32u);
x_31 = lean_uint64_of_nat(x_30);
x_32 = lean_uint64_shift_right(x_29, x_31);
x_33 = lean_uint64_xor(x_29, x_32);
x_34 = lean_unsigned_to_nat(16u);
x_35 = lean_uint64_of_nat(x_34);
x_36 = lean_uint64_shift_right(x_33, x_35);
x_37 = lean_uint64_xor(x_33, x_36);
x_38 = lean_uint64_to_usize(x_37);
x_39 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_usize_of_nat(x_40);
x_42 = lean_usize_sub(x_39, x_41);
x_43 = lean_usize_land(x_38, x_42);
x_44 = lean_array_uget(x_1, x_43);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_25);
lean_ctor_set(x_45, 1, x_26);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_array_uset(x_1, x_43, x_45);
x_1 = x_46;
x_2 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2_spec__2_spec__2___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2_spec__2___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_shiftl(x_3, x_4);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_box(0);
x_8 = lean_mk_array(x_5, x_7);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2_spec__2___redArg(x_6, x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; lean_object* x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; size_t x_45; size_t x_46; lean_object* x_47; size_t x_48; size_t x_49; size_t x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_64; 
x_33 = lean_ctor_get(x_4, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
x_35 = lean_array_get_size(x_34);
x_36 = lean_uint64_of_nat(x_3);
x_37 = lean_unsigned_to_nat(32u);
x_38 = lean_uint64_of_nat(x_37);
x_39 = lean_uint64_shift_right(x_36, x_38);
x_40 = lean_uint64_xor(x_36, x_39);
x_41 = lean_unsigned_to_nat(16u);
x_42 = lean_uint64_of_nat(x_41);
x_43 = lean_uint64_shift_right(x_40, x_42);
x_44 = lean_uint64_xor(x_40, x_43);
x_45 = lean_uint64_to_usize(x_44);
x_46 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_usize_of_nat(x_47);
x_49 = lean_usize_sub(x_46, x_48);
x_50 = lean_usize_land(x_45, x_49);
x_51 = lean_array_uget(x_34, x_50);
x_52 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__1___redArg(x_3, x_51);
if (x_52 == 0)
{
if (x_52 == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_4);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_77 = lean_ctor_get(x_4, 1);
lean_dec(x_77);
x_78 = lean_ctor_get(x_4, 0);
lean_dec(x_78);
x_79 = lean_box(0);
x_80 = lean_nat_add(x_33, x_47);
lean_dec(x_33);
lean_inc(x_3);
x_81 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_81, 0, x_3);
lean_ctor_set(x_81, 1, x_79);
lean_ctor_set(x_81, 2, x_51);
x_82 = lean_array_uset(x_34, x_50, x_81);
x_83 = lean_unsigned_to_nat(2u);
x_84 = lean_nat_shiftl(x_80, x_83);
x_85 = lean_unsigned_to_nat(3u);
x_86 = lean_nat_div(x_84, x_85);
lean_dec(x_84);
x_87 = lean_array_get_size(x_82);
x_88 = lean_nat_dec_le(x_86, x_87);
lean_dec(x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2___redArg(x_2, x_82);
lean_ctor_set(x_4, 1, x_89);
lean_ctor_set(x_4, 0, x_80);
x_64 = x_4;
goto block_75;
}
else
{
lean_ctor_set(x_4, 1, x_82);
lean_ctor_set(x_4, 0, x_80);
x_64 = x_4;
goto block_75;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
lean_dec(x_4);
x_90 = lean_box(0);
x_91 = lean_nat_add(x_33, x_47);
lean_dec(x_33);
lean_inc(x_3);
x_92 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_92, 0, x_3);
lean_ctor_set(x_92, 1, x_90);
lean_ctor_set(x_92, 2, x_51);
x_93 = lean_array_uset(x_34, x_50, x_92);
x_94 = lean_unsigned_to_nat(2u);
x_95 = lean_nat_shiftl(x_91, x_94);
x_96 = lean_unsigned_to_nat(3u);
x_97 = lean_nat_div(x_95, x_96);
lean_dec(x_95);
x_98 = lean_array_get_size(x_93);
x_99 = lean_nat_dec_le(x_97, x_98);
lean_dec(x_98);
lean_dec(x_97);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2___redArg(x_2, x_93);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_91);
lean_ctor_set(x_101, 1, x_100);
x_64 = x_101;
goto block_75;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_91);
lean_ctor_set(x_102, 1, x_93);
x_64 = x_102;
goto block_75;
}
}
}
else
{
lean_dec(x_51);
lean_dec(x_34);
lean_dec(x_33);
x_64 = x_4;
goto block_75;
}
}
else
{
lean_object* x_103; 
lean_dec(x_51);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_3);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_1);
lean_ctor_set(x_103, 1, x_4);
return x_103;
}
block_32:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_10 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_11 = lean_mk_string_unchecked(" -> ", 4, 4);
lean_inc(x_10);
x_12 = lean_string_append(x_10, x_11);
lean_inc(x_5);
x_13 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(x_6);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked("; ", 2, 2);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_string_append(x_18, x_10);
lean_dec(x_10);
x_20 = lean_string_append(x_19, x_11);
lean_dec(x_11);
lean_inc(x_8);
x_21 = l___private_Init_Data_Repr_0__Nat_reprFast(x_8);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(x_9);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_25 = lean_mk_string_unchecked(";", 1, 1);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = lean_string_append(x_1, x_26);
lean_dec(x_26);
x_28 = l_Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1___redArg(x_27, x_2, x_5, x_7);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_1 = x_29;
x_3 = x_8;
x_4 = x_30;
goto _start;
}
block_63:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_nat_shiftr(x_55, x_47);
x_58 = lean_nat_land(x_47, x_55);
lean_dec(x_55);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_nat_dec_eq(x_58, x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_box(1);
x_62 = lean_unbox(x_61);
x_5 = x_53;
x_6 = x_56;
x_7 = x_54;
x_8 = x_57;
x_9 = x_62;
goto block_32;
}
else
{
x_5 = x_53;
x_6 = x_56;
x_7 = x_54;
x_8 = x_57;
x_9 = x_52;
goto block_32;
}
}
block_75:
{
lean_object* x_65; 
x_65 = lean_array_fget(x_2, x_3);
if (lean_obj_tag(x_65) == 2)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_nat_shiftr(x_66, x_47);
x_69 = lean_nat_land(x_47, x_66);
lean_dec(x_66);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_nat_dec_eq(x_69, x_70);
lean_dec(x_69);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_box(1);
x_73 = lean_unbox(x_72);
x_53 = x_68;
x_54 = x_64;
x_55 = x_67;
x_56 = x_73;
goto block_63;
}
else
{
x_53 = x_68;
x_54 = x_64;
x_55 = x_67;
x_56 = x_52;
goto block_63;
}
}
else
{
lean_object* x_74; 
lean_dec(x_65);
lean_dec(x_3);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_64);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1___redArg(x_1, x_2, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_array_fget(x_1, x_2);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
x_5 = lean_mk_string_unchecked(" [label=\"", 9, 9);
x_6 = lean_string_append(x_4, x_5);
lean_dec(x_5);
x_7 = lean_mk_string_unchecked("false", 5, 5);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_mk_string_unchecked("\", shape=box];", 14, 14);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
x_13 = lean_mk_string_unchecked(" [label=\"", 9, 9);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_mk_string_unchecked("x", 1, 1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = l___private_Init_Data_Repr_0__Nat_reprFast(x_16);
x_18 = lean_string_append(x_15, x_17);
lean_dec(x_17);
x_19 = lean_mk_string_unchecked("[", 1, 1);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = lean_ctor_get(x_11, 2);
lean_inc(x_21);
lean_dec(x_11);
x_22 = l___private_Init_Data_Repr_0__Nat_reprFast(x_21);
x_23 = lean_string_append(x_20, x_22);
lean_dec(x_22);
x_24 = lean_mk_string_unchecked("]", 1, 1);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = lean_string_append(x_14, x_25);
lean_dec(x_25);
x_27 = lean_mk_string_unchecked("\", shape=doublecircle];", 23, 23);
x_28 = lean_string_append(x_26, x_27);
lean_dec(x_27);
return x_28;
}
default: 
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_3);
x_29 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
x_30 = lean_mk_string_unchecked(" [label=\"", 9, 9);
lean_inc(x_29);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = lean_string_append(x_31, x_29);
lean_dec(x_29);
x_33 = lean_mk_string_unchecked(" ∧\",shape=trapezium];", 23, 21);
x_34 = lean_string_append(x_32, x_33);
lean_dec(x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__6(x_1, x_4);
x_7 = lean_string_append(x_2, x_6);
lean_dec(x_6);
x_2 = x_7;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__7(x_1, x_5, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_5 = x_8;
goto _start;
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_dec(x_6);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_mk_string_unchecked("", 0, 0);
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
lean_ctor_set(x_2, 1, x_17);
lean_ctor_set(x_2, 0, x_10);
lean_inc(x_8);
x_18 = l_Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1___redArg(x_8, x_5, x_7, x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_array_get_size(x_28);
x_30 = lean_nat_dec_lt(x_10, x_29);
if (x_30 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_5);
x_21 = x_8;
goto block_27;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_29, x_29);
if (x_31 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_5);
x_21 = x_8;
goto block_27;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; 
x_32 = lean_usize_of_nat(x_10);
x_33 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_34 = l_Array_foldlMUnsafe_fold___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__8(x_5, x_28, x_32, x_33, x_8);
lean_dec(x_28);
lean_dec(x_5);
x_21 = x_34;
goto block_27;
}
}
block_27:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_mk_string_unchecked("Digraph AIG {", 13, 13);
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = lean_string_append(x_23, x_19);
lean_dec(x_19);
x_25 = lean_mk_string_unchecked("}", 1, 1);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
return x_26;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_35 = lean_ctor_get(x_2, 0);
lean_inc(x_35);
lean_dec(x_2);
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
lean_dec(x_3);
x_37 = lean_mk_string_unchecked("", 0, 0);
x_38 = lean_unsigned_to_nat(8u);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_unsigned_to_nat(2u);
x_41 = lean_nat_shiftl(x_38, x_40);
x_42 = lean_unsigned_to_nat(3u);
x_43 = lean_nat_div(x_41, x_42);
lean_dec(x_41);
x_44 = l_Nat_nextPowerOfTwo(x_43);
lean_dec(x_43);
x_45 = lean_box(0);
x_46 = lean_mk_array(x_44, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_46);
lean_inc(x_37);
x_48 = l_Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1___redArg(x_37, x_35, x_36, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_dec(x_50);
x_59 = lean_array_get_size(x_58);
x_60 = lean_nat_dec_lt(x_39, x_59);
if (x_60 == 0)
{
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_35);
x_51 = x_37;
goto block_57;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_59, x_59);
if (x_61 == 0)
{
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_35);
x_51 = x_37;
goto block_57;
}
else
{
size_t x_62; size_t x_63; lean_object* x_64; 
x_62 = lean_usize_of_nat(x_39);
x_63 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_64 = l_Array_foldlMUnsafe_fold___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__8(x_35, x_58, x_62, x_63, x_37);
lean_dec(x_58);
lean_dec(x_35);
x_51 = x_64;
goto block_57;
}
}
block_57:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_mk_string_unchecked("Digraph AIG {", 13, 13);
x_53 = lean_string_append(x_52, x_51);
lean_dec(x_51);
x_54 = lean_string_append(x_53, x_49);
lean_dec(x_49);
x_55 = lean_mk_string_unchecked("}", 1, 1);
x_56 = lean_string_append(x_54, x_55);
lean_dec(x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_mk_string_unchecked("Bitblasting BVLogicalExpr to AIG", 32, 32);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_MessageData_ofFormat(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_IO_lazyPure___redArg(x_1, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Std_Sat_AIG_Entrypoint_relabelNat_x27___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__0(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Std_Sat_AIG_toCNF(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = l_Std_Sat_AIG_toCNF(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_mk_string_unchecked("Converting AIG to CNF", 21, 21);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_MessageData_ofFormat(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_mk_string_unchecked("Obtaining external proof certificate", 36, 36);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_MessageData_ofFormat(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_IO_lazyPure___redArg(x_1, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_BVDecide_Frontend_runExternal(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__0___boxed), 6, 0);
x_32 = lean_ctor_get(x_3, 0);
lean_inc(x_32);
x_33 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__1___boxed), 2, 1);
lean_closure_set(x_33, 0, x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__2___boxed), 6, 1);
lean_closure_set(x_34, 0, x_33);
x_35 = lean_mk_string_unchecked("Meta", 4, 4);
x_36 = lean_mk_string_unchecked("Tactic", 6, 6);
x_37 = lean_mk_string_unchecked("bv", 2, 2);
lean_inc(x_36);
lean_inc(x_35);
x_38 = l_Lean_Name_mkStr3(x_35, x_36, x_37);
x_39 = lean_box(1);
x_40 = lean_mk_string_unchecked("", 0, 0);
x_41 = lean_unbox(x_39);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_40);
lean_inc(x_38);
x_42 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_38, x_31, x_34, x_41, x_40, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_150; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_38);
x_45 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_38, x_5, x_6, x_7, x_8, x_44);
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
lean_inc(x_43);
x_49 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__3___boxed), 2, 1);
lean_closure_set(x_49, 0, x_43);
x_50 = lean_ctor_get(x_43, 0);
lean_inc(x_50);
x_51 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__4___boxed), 6, 0);
x_52 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__5___boxed), 6, 0);
x_53 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__6___boxed), 6, 1);
lean_closure_set(x_53, 0, x_49);
x_54 = lean_ctor_get(x_50, 0);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_array_get_size(x_54);
lean_dec(x_54);
x_150 = lean_unbox(x_46);
lean_dec(x_46);
if (x_150 == 0)
{
lean_dec(x_38);
x_121 = x_5;
x_122 = x_6;
x_123 = x_7;
x_124 = x_8;
x_125 = x_47;
goto block_149;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_151 = lean_mk_string_unchecked("AIG has ", 8, 8);
lean_inc(x_55);
x_152 = l___private_Init_Data_Repr_0__Nat_reprFast(x_55);
x_153 = lean_string_append(x_151, x_152);
lean_dec(x_152);
x_154 = lean_mk_string_unchecked(" nodes.", 7, 7);
x_155 = lean_string_append(x_153, x_154);
lean_dec(x_154);
x_156 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_156, 0, x_155);
x_157 = l_Lean_MessageData_ofFormat(x_156);
x_158 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_38, x_157, x_5, x_6, x_7, x_8, x_47);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec(x_158);
x_121 = x_5;
x_122 = x_6;
x_123 = x_7;
x_124 = x_8;
x_125 = x_159;
goto block_149;
}
block_64:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = l_Lean_Elab_Tactic_BVDecide_Frontend_reconstructCounterExample(x_56, x_57, x_55, x_4);
lean_dec(x_55);
lean_dec(x_57);
x_60 = lean_ctor_get(x_3, 2);
lean_inc(x_60);
lean_dec(x_3);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_61, 2, x_59);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
if (lean_is_scalar(x_48)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_48;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_58);
return x_63;
}
block_120:
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_70 = lean_mk_string_unchecked("sat", 3, 3);
x_71 = l_Lean_Name_mkStr3(x_35, x_36, x_70);
x_72 = lean_unbox(x_39);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_40);
lean_inc(x_71);
x_73 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_71, x_51, x_53, x_72, x_40, x_65, x_66, x_67, x_68, x_69);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_ctor_get(x_2, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_2, 4);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 5);
lean_inc(x_80);
x_81 = lean_ctor_get_uint8(x_80, sizeof(void*)*2);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
x_83 = lean_ctor_get_uint8(x_80, sizeof(void*)*2 + 1);
lean_dec(x_80);
x_84 = lean_box(x_81);
x_85 = lean_box(x_83);
x_86 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__7___boxed), 11, 6);
lean_closure_set(x_86, 0, x_76);
lean_closure_set(x_86, 1, x_78);
lean_closure_set(x_86, 2, x_79);
lean_closure_set(x_86, 3, x_84);
lean_closure_set(x_86, 4, x_82);
lean_closure_set(x_86, 5, x_85);
x_87 = lean_unbox(x_39);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_71);
x_88 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_71, x_52, x_86, x_87, x_40, x_65, x_66, x_67, x_68, x_75);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec(x_2);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_71);
x_92 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_71, x_65, x_66, x_67, x_68, x_90);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; 
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_56 = x_77;
x_57 = x_91;
x_58 = x_95;
goto block_64;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec(x_92);
x_97 = lean_mk_string_unchecked("SAT solver found a counter example.", 35, 35);
x_98 = l_Lean_stringToMessageData(x_97);
lean_dec(x_97);
x_99 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_71, x_98, x_65, x_66, x_67, x_68, x_96);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_56 = x_77;
x_57 = x_91;
x_58 = x_100;
goto block_64;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_dec(x_77);
lean_dec(x_55);
lean_dec(x_48);
lean_dec(x_1);
x_101 = lean_ctor_get(x_88, 1);
lean_inc(x_101);
lean_dec(x_88);
x_102 = lean_ctor_get(x_89, 0);
lean_inc(x_102);
lean_dec(x_89);
lean_inc(x_71);
x_103 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_71, x_65, x_66, x_67, x_68, x_101);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; 
lean_dec(x_71);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_10 = x_102;
x_11 = x_65;
x_12 = x_66;
x_13 = x_67;
x_14 = x_68;
x_15 = x_106;
goto block_30;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_ctor_get(x_103, 1);
lean_inc(x_107);
lean_dec(x_103);
x_108 = lean_mk_string_unchecked("SAT solver found a proof.", 25, 25);
x_109 = l_Lean_stringToMessageData(x_108);
lean_dec(x_108);
x_110 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_71, x_109, x_65, x_66, x_67, x_68, x_107);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_10 = x_102;
x_11 = x_65;
x_12 = x_66;
x_13 = x_67;
x_14 = x_68;
x_15 = x_111;
goto block_30;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_77);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_55);
lean_dec(x_48);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_88);
if (x_112 == 0)
{
return x_88;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_88, 0);
x_114 = lean_ctor_get(x_88, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_88);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_48);
lean_dec(x_40);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_73);
if (x_116 == 0)
{
return x_73;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_73, 0);
x_118 = lean_ctor_get(x_73, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_73);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
block_149:
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_ctor_get(x_2, 5);
lean_inc(x_126);
x_127 = lean_ctor_get_uint8(x_126, sizeof(void*)*2 + 8);
lean_dec(x_126);
if (x_127 == 0)
{
lean_dec(x_43);
x_65 = x_121;
x_66 = x_122;
x_67 = x_123;
x_68 = x_124;
x_69 = x_125;
goto block_120;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_mk_string_unchecked(".", 1, 1);
x_129 = lean_mk_string_unchecked("aig.gv", 6, 6);
x_130 = l_System_FilePath_join(x_128, x_129);
lean_dec(x_129);
x_131 = l_Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1(x_43);
x_132 = l_IO_FS_writeFile(x_130, x_131, x_125);
lean_dec(x_131);
lean_dec(x_130);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_65 = x_121;
x_66 = x_122;
x_67 = x_123;
x_68 = x_124;
x_69 = x_133;
goto block_120;
}
else
{
uint8_t x_134; 
lean_dec(x_124);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_40);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_134 = !lean_is_exclusive(x_132);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_135 = lean_ctor_get(x_132, 0);
x_136 = lean_ctor_get(x_123, 5);
lean_inc(x_136);
lean_dec(x_123);
x_137 = lean_io_error_to_string(x_135);
x_138 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_138, 0, x_137);
x_139 = l_Lean_MessageData_ofFormat(x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_136);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_132, 0, x_140);
return x_132;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_141 = lean_ctor_get(x_132, 0);
x_142 = lean_ctor_get(x_132, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_132);
x_143 = lean_ctor_get(x_123, 5);
lean_inc(x_143);
lean_dec(x_123);
x_144 = lean_io_error_to_string(x_141);
x_145 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_146 = l_Lean_MessageData_ofFormat(x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_143);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_142);
return x_148;
}
}
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_160 = !lean_is_exclusive(x_42);
if (x_160 == 0)
{
return x_42;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_42, 0);
x_162 = lean_ctor_get(x_42, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_42);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
block_30:
{
lean_object* x_16; 
lean_inc(x_10);
x_16 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof(x_10, x_2, x_3, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_10);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_10);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_10);
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1_spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Sat_AIG_toGraphviz_go___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__6(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__7(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Std_Sat_AIG_toGraphviz___at___Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster_spec__1_spec__8(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___lam__7(x_1, x_2, x_3, x_12, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_3, x_2);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_mk_empty_array_with_capacity(x_20);
x_22 = lean_array_uget(x_1, x_3);
lean_inc(x_22);
x_23 = l_Lean_Expr_fvar___override(x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___boxed), 8, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_unsigned_to_nat(8u);
x_26 = lean_unsigned_to_nat(2u);
x_27 = lean_nat_shiftl(x_25, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_nat_div(x_27, x_28);
lean_dec(x_27);
x_30 = l_Nat_nextPowerOfTwo(x_29);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = lean_mk_array(x_30, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_32);
lean_inc_n(x_33, 2);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_33);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_35 = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_run___redArg(x_24, x_34, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_40 = x_36;
} else {
 lean_dec_ref(x_36);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_4, 0);
lean_inc(x_41);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; lean_object* x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; size_t x_58; size_t x_59; lean_object* x_60; size_t x_61; size_t x_62; size_t x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_39);
x_45 = lean_ctor_get(x_4, 1);
lean_inc(x_45);
lean_dec(x_4);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
x_48 = lean_array_get_size(x_47);
x_49 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_22);
x_50 = lean_unsigned_to_nat(32u);
x_51 = lean_uint64_of_nat(x_50);
x_52 = lean_uint64_shift_right(x_49, x_51);
x_53 = lean_uint64_xor(x_49, x_52);
x_54 = lean_unsigned_to_nat(16u);
x_55 = lean_uint64_of_nat(x_54);
x_56 = lean_uint64_shift_right(x_53, x_55);
x_57 = lean_uint64_xor(x_53, x_56);
x_58 = lean_uint64_to_usize(x_57);
x_59 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_usize_of_nat(x_60);
x_62 = lean_usize_sub(x_59, x_61);
x_63 = lean_usize_land(x_58, x_62);
x_64 = lean_array_uget(x_47, x_63);
x_65 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_MVarId_getNondepPropHyps_spec__0___redArg(x_22, x_64);
if (x_65 == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_45);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_67 = lean_ctor_get(x_45, 1);
lean_dec(x_67);
x_68 = lean_ctor_get(x_45, 0);
lean_dec(x_68);
x_69 = lean_box(0);
x_70 = lean_nat_add(x_46, x_60);
lean_dec(x_46);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_22);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_71, 2, x_64);
x_72 = lean_array_uset(x_47, x_63, x_71);
x_73 = lean_nat_shiftl(x_70, x_26);
x_74 = lean_nat_div(x_73, x_28);
lean_dec(x_73);
x_75 = lean_array_get_size(x_72);
x_76 = lean_nat_dec_le(x_74, x_75);
lean_dec(x_75);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_MVarId_getNondepPropHyps_spec__6___redArg(x_72);
lean_ctor_set(x_45, 1, x_77);
lean_ctor_set(x_45, 0, x_70);
x_42 = x_45;
goto block_44;
}
else
{
lean_ctor_set(x_45, 1, x_72);
lean_ctor_set(x_45, 0, x_70);
x_42 = x_45;
goto block_44;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
lean_dec(x_45);
x_78 = lean_box(0);
x_79 = lean_nat_add(x_46, x_60);
lean_dec(x_46);
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_22);
lean_ctor_set(x_80, 1, x_78);
lean_ctor_set(x_80, 2, x_64);
x_81 = lean_array_uset(x_47, x_63, x_80);
x_82 = lean_nat_shiftl(x_79, x_26);
x_83 = lean_nat_div(x_82, x_28);
lean_dec(x_82);
x_84 = lean_array_get_size(x_81);
x_85 = lean_nat_dec_le(x_83, x_84);
lean_dec(x_84);
lean_dec(x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_MVarId_getNondepPropHyps_spec__6___redArg(x_81);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_86);
x_42 = x_87;
goto block_44;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_79);
lean_ctor_set(x_88, 1, x_81);
x_42 = x_88;
goto block_44;
}
}
}
else
{
lean_dec(x_64);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_22);
x_42 = x_45;
goto block_44;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_40);
lean_dec(x_22);
x_89 = lean_ctor_get(x_4, 1);
lean_inc(x_89);
lean_dec(x_4);
x_90 = lean_ctor_get(x_38, 0);
lean_inc(x_90);
lean_dec(x_38);
x_91 = l_Array_append(lean_box(0), x_41, x_39);
lean_dec(x_39);
x_92 = lean_array_push(x_91, x_90);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_89);
x_11 = x_93;
x_12 = x_37;
goto block_17;
}
block_44:
{
lean_object* x_43; 
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_11 = x_43;
x_12 = x_37;
goto block_17;
}
}
else
{
uint8_t x_94; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_35);
if (x_94 == 0)
{
return x_35;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_35, 0);
x_96 = lean_ctor_get(x_35, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_35);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
block_17:
{
lean_object* x_13; size_t x_14; size_t x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_4 = x_11;
x_10 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and(x_4, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__2___redArg___lam__0), 7, 2);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_reflectBV___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_getPropHyps(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = lean_unsigned_to_nat(8u);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_shiftl(x_12, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_17 = l_Nat_nextPowerOfTwo(x_16);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = lean_mk_array(x_17, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_size(x_8);
x_23 = lean_usize_of_nat(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_24 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__0(x_8, x_22, x_23, x_21, x_1, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_38; uint8_t x_39; 
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
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_38 = lean_array_get_size(x_28);
x_39 = lean_nat_dec_eq(x_38, x_10);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_array_fget(x_28, x_10);
x_41 = lean_unsigned_to_nat(1u);
x_42 = l_Array_toSubarray___redArg(x_28, x_41, x_38);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 2);
lean_inc(x_44);
x_45 = lean_nat_dec_lt(x_43, x_44);
if (x_45 == 0)
{
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_30 = x_40;
goto block_37;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_array_get_size(x_46);
x_48 = lean_nat_dec_le(x_44, x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_43);
x_30 = x_40;
goto block_37;
}
else
{
size_t x_49; size_t x_50; lean_object* x_51; 
x_49 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_50 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_51 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__1(x_46, x_49, x_50, x_40);
lean_dec(x_46);
x_30 = x_51;
goto block_37;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_38);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_52 = lean_mk_string_unchecked("None of the hypotheses are in the supported BitVec fragment.\nThere are two potential fixes for this:\n1. If you are using custom BitVec constructs simplify them to built-in ones.\n2. If your problem is using only built-in ones it might currently be out of reach.\n   Consider expressing it in terms of different operations that are better supported.", 346, 346);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_MessageData_ofFormat(x_53);
x_55 = l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg(x_54, x_2, x_3, x_4, x_5, x_26);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_55;
}
block_37:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = l_Lean_ShareCommon_shareCommon(lean_box(0), x_31);
lean_inc(x_30);
x_33 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse), 8, 1);
lean_closure_set(x_33, 0, x_30);
x_34 = lean_ctor_get(x_30, 2);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_34);
if (lean_is_scalar(x_27)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_27;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
return x_36;
}
}
else
{
uint8_t x_56; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_24);
if (x_56 == 0)
{
return x_24;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_24, 0);
x_58 = lean_ctor_get(x_24, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_24);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_7);
if (x_60 == 0)
{
return x_7;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_7, 0);
x_62 = lean_ctor_get(x_7, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_7);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_reflectBV(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_reflectBV___lam__0), 6, 0);
x_9 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__2___redArg(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_reflectBV___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_reflectBV(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__0___redArg(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__2___redArg(x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg___lam__0(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg___lam__1(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__1___redArg(x_1, x_5, x_2, x_3, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__2___redArg(x_4, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; double x_14; uint8_t x_15; double x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; double x_33; lean_object* x_34; double x_35; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; double x_56; lean_object* x_57; lean_object* x_58; double x_59; uint8_t x_60; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; double x_86; lean_object* x_87; lean_object* x_88; double x_89; double x_90; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; double x_100; double x_101; lean_object* x_102; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_201; 
lean_inc(x_1);
x_48 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg(x_1, x_9, x_11);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_94 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg___lam__0), 1, 0);
x_95 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg___lam__1), 1, 0);
x_96 = lean_ctor_get(x_9, 2);
lean_inc(x_96);
x_201 = lean_unbox(x_49);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = l_Lean_trace_profiler;
x_203 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_96, x_202);
if (x_203 == 0)
{
lean_object* x_204; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_204 = lean_apply_6(x_3, x_6, x_7, x_8, x_9, x_10, x_50);
return x_204;
}
else
{
goto block_200;
}
}
else
{
goto block_200;
}
block_28:
{
lean_object* x_20; 
x_20 = lean_unsigned_to_nat(0u);
if (x_15 == 0)
{
double x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_float_of_nat(x_20);
x_22 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_5);
lean_ctor_set_float(x_22, sizeof(void*)*2, x_21);
lean_ctor_set_float(x_22, sizeof(void*)*2 + 8, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 16, x_4);
x_23 = lean_box(0);
x_24 = l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg___lam__2(x_13, x_17, x_18, x_12, x_22, x_23, x_6, x_7, x_8, x_9, x_10, x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_5);
lean_ctor_set_float(x_25, sizeof(void*)*2, x_14);
lean_ctor_set_float(x_25, sizeof(void*)*2 + 8, x_16);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 16, x_4);
x_26 = lean_box(0);
x_27 = l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg___lam__2(x_13, x_17, x_18, x_12, x_25, x_26, x_6, x_7, x_8, x_9, x_10, x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_12);
return x_27;
}
}
block_47:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_9, 5);
lean_inc(x_36);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_37 = lean_apply_7(x_2, x_31, x_6, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_37) == 0)
{
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_12 = x_29;
x_13 = x_30;
x_14 = x_33;
x_15 = x_32;
x_16 = x_35;
x_17 = x_36;
x_18 = x_38;
x_19 = x_39;
goto block_28;
}
else
{
uint8_t x_40; 
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_ctor_set_tag(x_37, 1);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_dec(x_37);
x_45 = lean_mk_string_unchecked("<exception thrown while producing trace node message>", 53, 53);
x_46 = l_Lean_stringToMessageData(x_45);
lean_dec(x_45);
x_12 = x_29;
x_13 = x_30;
x_14 = x_33;
x_15 = x_32;
x_16 = x_35;
x_17 = x_36;
x_18 = x_46;
x_19 = x_44;
goto block_28;
}
}
block_81:
{
uint8_t x_61; 
x_61 = lean_unbox(x_49);
lean_dec(x_49);
if (x_61 == 0)
{
if (x_60 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint64_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_st_ref_take(x_10, x_58);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_63, 3);
lean_inc(x_68);
x_69 = lean_ctor_get_uint64(x_68, sizeof(void*)*1);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_PersistentArray_append___redArg(x_57, x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set_uint64(x_72, sizeof(void*)*1, x_69);
x_73 = lean_ctor_get(x_63, 4);
lean_inc(x_73);
x_74 = lean_ctor_get(x_63, 5);
lean_inc(x_74);
x_75 = lean_ctor_get(x_63, 6);
lean_inc(x_75);
x_76 = lean_ctor_get(x_63, 7);
lean_inc(x_76);
lean_dec(x_63);
x_77 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_77, 0, x_65);
lean_ctor_set(x_77, 1, x_66);
lean_ctor_set(x_77, 2, x_67);
lean_ctor_set(x_77, 3, x_72);
lean_ctor_set(x_77, 4, x_73);
lean_ctor_set(x_77, 5, x_74);
lean_ctor_set(x_77, 6, x_75);
lean_ctor_set(x_77, 7, x_76);
x_78 = lean_st_ref_set(x_10, x_77, x_64);
lean_dec(x_10);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__2___redArg(x_55, x_79);
lean_dec(x_55);
return x_80;
}
else
{
lean_dec(x_57);
x_29 = x_52;
x_30 = x_53;
x_31 = x_55;
x_32 = x_54;
x_33 = x_56;
x_34 = x_58;
x_35 = x_59;
goto block_47;
}
}
else
{
lean_dec(x_57);
x_29 = x_52;
x_30 = x_53;
x_31 = x_55;
x_32 = x_54;
x_33 = x_56;
x_34 = x_58;
x_35 = x_59;
goto block_47;
}
}
block_93:
{
double x_91; uint8_t x_92; 
x_91 = lean_float_sub(x_89, x_86);
x_92 = lean_float_decLt(x_90, x_91);
x_52 = x_82;
x_53 = x_83;
x_54 = x_85;
x_55 = x_84;
x_56 = x_86;
x_57 = x_87;
x_58 = x_88;
x_59 = x_89;
x_60 = x_92;
goto block_81;
}
block_116:
{
lean_object* x_103; uint8_t x_104; 
x_103 = l_Lean_trace_profiler;
x_104 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_96, x_103);
if (x_104 == 0)
{
lean_dec(x_96);
lean_inc(x_99);
x_52 = x_99;
x_53 = x_97;
x_54 = x_104;
x_55 = x_99;
x_56 = x_100;
x_57 = x_98;
x_58 = x_102;
x_59 = x_101;
x_60 = x_104;
goto block_81;
}
else
{
lean_object* x_105; uint8_t x_106; 
x_105 = l_Lean_trace_profiler_useHeartbeats;
x_106 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_96, x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; double x_109; lean_object* x_110; double x_111; double x_112; 
x_107 = l_Lean_trace_profiler_threshold;
x_108 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_96, x_107);
lean_dec(x_96);
x_109 = lean_float_of_nat(x_108);
x_110 = lean_unsigned_to_nat(1000u);
x_111 = lean_float_of_nat(x_110);
x_112 = lean_float_div(x_109, x_111);
lean_inc(x_99);
x_82 = x_99;
x_83 = x_97;
x_84 = x_99;
x_85 = x_104;
x_86 = x_100;
x_87 = x_98;
x_88 = x_102;
x_89 = x_101;
x_90 = x_112;
goto block_93;
}
else
{
lean_object* x_113; lean_object* x_114; double x_115; 
x_113 = l_Lean_trace_profiler_threshold;
x_114 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_96, x_113);
lean_dec(x_96);
x_115 = lean_float_of_nat(x_114);
lean_inc(x_99);
x_82 = x_99;
x_83 = x_97;
x_84 = x_99;
x_85 = x_104;
x_86 = x_100;
x_87 = x_98;
x_88 = x_102;
x_89 = x_101;
x_90 = x_115;
goto block_93;
}
}
}
block_146:
{
lean_object* x_124; 
x_124 = lean_apply_1(x_119, x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; double x_127; lean_object* x_128; double x_129; double x_130; double x_131; double x_132; 
lean_dec(x_120);
lean_dec(x_51);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_float_of_nat(x_117);
x_128 = lean_unsigned_to_nat(1000000000u);
x_129 = lean_float_of_nat(x_128);
x_130 = lean_float_div(x_127, x_129);
x_131 = lean_float_of_nat(x_125);
x_132 = lean_float_div(x_131, x_129);
x_97 = x_118;
x_98 = x_121;
x_99 = x_122;
x_100 = x_130;
x_101 = x_132;
x_102 = x_126;
goto block_116;
}
else
{
uint8_t x_133; 
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_96);
lean_dec(x_49);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_124);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_124, 0);
x_135 = lean_io_error_to_string(x_134);
x_136 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_137 = l_Lean_MessageData_ofFormat(x_136);
if (lean_is_scalar(x_51)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_51;
}
lean_ctor_set(x_138, 0, x_120);
lean_ctor_set(x_138, 1, x_137);
lean_ctor_set(x_124, 0, x_138);
return x_124;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_139 = lean_ctor_get(x_124, 0);
x_140 = lean_ctor_get(x_124, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_124);
x_141 = lean_io_error_to_string(x_139);
x_142 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_143 = l_Lean_MessageData_ofFormat(x_142);
if (lean_is_scalar(x_51)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_51;
}
lean_ctor_set(x_144, 0, x_120);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_140);
return x_145;
}
}
}
block_172:
{
lean_object* x_154; 
x_154 = lean_apply_1(x_149, x_153);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; double x_157; double x_158; 
lean_dec(x_151);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_float_of_nat(x_147);
x_158 = lean_float_of_nat(x_155);
x_97 = x_148;
x_98 = x_150;
x_99 = x_152;
x_100 = x_157;
x_101 = x_158;
x_102 = x_156;
goto block_116;
}
else
{
uint8_t x_159; 
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_96);
lean_dec(x_49);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_159 = !lean_is_exclusive(x_154);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_160 = lean_ctor_get(x_154, 0);
x_161 = lean_io_error_to_string(x_160);
x_162 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_162, 0, x_161);
x_163 = l_Lean_MessageData_ofFormat(x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_151);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set(x_154, 0, x_164);
return x_154;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_165 = lean_ctor_get(x_154, 0);
x_166 = lean_ctor_get(x_154, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_154);
x_167 = lean_io_error_to_string(x_165);
x_168 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_168, 0, x_167);
x_169 = l_Lean_MessageData_ofFormat(x_168);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_151);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_166);
return x_171;
}
}
}
block_200:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_173 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__0___redArg(x_10, x_50);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = l_Lean_trace_profiler_useHeartbeats;
x_177 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_96, x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_94);
x_178 = lean_ctor_get(x_9, 5);
lean_inc(x_178);
x_179 = l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg___lam__1(x_175);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_182 = lean_apply_6(x_3, x_6, x_7, x_8, x_9, x_10, x_181);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_183);
lean_inc(x_174);
x_117 = x_180;
x_118 = x_174;
x_119 = x_95;
x_120 = x_178;
x_121 = x_174;
x_122 = x_185;
x_123 = x_184;
goto block_146;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_182, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_182, 1);
lean_inc(x_187);
lean_dec(x_182);
x_188 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_188, 0, x_186);
lean_inc(x_174);
x_117 = x_180;
x_118 = x_174;
x_119 = x_95;
x_120 = x_178;
x_121 = x_174;
x_122 = x_188;
x_123 = x_187;
goto block_146;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_95);
lean_dec(x_51);
x_189 = lean_ctor_get(x_9, 5);
lean_inc(x_189);
x_190 = l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg___lam__0(x_175);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_193 = lean_apply_6(x_3, x_6, x_7, x_8, x_9, x_10, x_192);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_194);
lean_inc(x_174);
x_147 = x_191;
x_148 = x_174;
x_149 = x_94;
x_150 = x_174;
x_151 = x_189;
x_152 = x_196;
x_153 = x_195;
goto block_172;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_193, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_193, 1);
lean_inc(x_198);
lean_dec(x_193);
x_199 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_199, 0, x_197);
lean_inc(x_174);
x_147 = x_191;
x_148 = x_174;
x_149 = x_94;
x_150 = x_174;
x_151 = x_189;
x_152 = x_199;
x_153 = x_198;
goto block_172;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_4, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
lean_dec(x_5);
x_14 = lean_box(x_13);
lean_ctor_set(x_4, 1, x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_16);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
lean_dec(x_5);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_25);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_4, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_29 = x_4;
} else {
 lean_dec_ref(x_4);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_5, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
lean_dec(x_5);
x_33 = lean_box(x_32);
if (lean_is_scalar(x_29)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_29;
}
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_2);
x_1 = x_27;
x_2 = x_37;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; size_t x_20; size_t x_21; lean_object* x_22; size_t x_23; size_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_array_get_size(x_9);
x_11 = lean_uint64_of_nat(x_5);
x_12 = lean_unsigned_to_nat(32u);
x_13 = lean_uint64_of_nat(x_12);
x_14 = lean_uint64_shift_right(x_11, x_13);
x_15 = lean_uint64_xor(x_11, x_14);
x_16 = lean_unsigned_to_nat(16u);
x_17 = lean_uint64_of_nat(x_16);
x_18 = lean_uint64_shift_right(x_15, x_17);
x_19 = lean_uint64_xor(x_15, x_18);
x_20 = lean_uint64_to_usize(x_19);
x_21 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_usize_of_nat(x_22);
x_24 = lean_usize_sub(x_21, x_23);
x_25 = lean_usize_land(x_20, x_24);
x_26 = lean_array_uget(x_9, x_25);
x_27 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0___redArg(x_5, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_28 = lean_nat_add(x_8, x_22);
lean_dec(x_8);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_5);
lean_ctor_set(x_29, 1, x_6);
lean_ctor_set(x_29, 2, x_26);
x_30 = lean_array_uset(x_9, x_25, x_29);
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_nat_shiftl(x_28, x_31);
x_33 = lean_unsigned_to_nat(3u);
x_34 = lean_nat_div(x_32, x_33);
lean_dec(x_32);
x_35 = lean_array_get_size(x_30);
x_36 = lean_nat_dec_le(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__1___redArg(x_30);
lean_ctor_set(x_2, 1, x_37);
lean_ctor_set(x_2, 0, x_28);
x_1 = x_4;
goto _start;
}
else
{
lean_ctor_set(x_2, 1, x_30);
lean_ctor_set(x_2, 0, x_28);
x_1 = x_4;
goto _start;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_box(0);
x_41 = lean_array_uset(x_9, x_25, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__4(lean_box(0), x_5, x_6, x_26);
x_43 = lean_array_uset(x_41, x_25, x_42);
lean_ctor_set(x_2, 1, x_43);
x_1 = x_4;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; lean_object* x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; size_t x_57; size_t x_58; lean_object* x_59; size_t x_60; size_t x_61; size_t x_62; lean_object* x_63; uint8_t x_64; 
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get(x_2, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_2);
x_47 = lean_array_get_size(x_46);
x_48 = lean_uint64_of_nat(x_5);
x_49 = lean_unsigned_to_nat(32u);
x_50 = lean_uint64_of_nat(x_49);
x_51 = lean_uint64_shift_right(x_48, x_50);
x_52 = lean_uint64_xor(x_48, x_51);
x_53 = lean_unsigned_to_nat(16u);
x_54 = lean_uint64_of_nat(x_53);
x_55 = lean_uint64_shift_right(x_52, x_54);
x_56 = lean_uint64_xor(x_52, x_55);
x_57 = lean_uint64_to_usize(x_56);
x_58 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_usize_of_nat(x_59);
x_61 = lean_usize_sub(x_58, x_60);
x_62 = lean_usize_land(x_57, x_61);
x_63 = lean_array_uget(x_46, x_62);
x_64 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__0___redArg(x_5, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_65 = lean_nat_add(x_45, x_59);
lean_dec(x_45);
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_5);
lean_ctor_set(x_66, 1, x_6);
lean_ctor_set(x_66, 2, x_63);
x_67 = lean_array_uset(x_46, x_62, x_66);
x_68 = lean_unsigned_to_nat(2u);
x_69 = lean_nat_shiftl(x_65, x_68);
x_70 = lean_unsigned_to_nat(3u);
x_71 = lean_nat_div(x_69, x_70);
lean_dec(x_69);
x_72 = lean_array_get_size(x_67);
x_73 = lean_nat_dec_le(x_71, x_72);
lean_dec(x_72);
lean_dec(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__1___redArg(x_67);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_65);
lean_ctor_set(x_75, 1, x_74);
x_1 = x_4;
x_2 = x_75;
goto _start;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_65);
lean_ctor_set(x_77, 1, x_67);
x_1 = x_4;
x_2 = x_77;
goto _start;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_box(0);
x_80 = lean_array_uset(x_46, x_62, x_79);
x_81 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run_spec__4(lean_box(0), x_5, x_6, x_63);
x_82 = lean_array_uset(x_80, x_62, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_45);
lean_ctor_set(x_83, 1, x_82);
x_1 = x_4;
x_2 = x_83;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__5___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 6);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 7);
lean_inc(x_16);
x_17 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_16, x_1, x_2);
x_18 = lean_ctor_get(x_8, 8);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_12);
lean_ctor_set(x_19, 4, x_13);
lean_ctor_set(x_19, 5, x_14);
lean_ctor_set(x_19, 6, x_15);
lean_ctor_set(x_19, 7, x_17);
lean_ctor_set(x_19, 8, x_18);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_6, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_6, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_6, 4);
lean_inc(x_23);
lean_dec(x_6);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
lean_ctor_set(x_24, 4, x_23);
x_25 = lean_st_ref_set(x_3, x_24, x_7);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_assign___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__6___redArg(x_1, x_2, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__7(x_1, x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_sub(x_2, x_7);
x_9 = lean_array_uget(x_1, x_8);
x_10 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__7(x_4, x_9);
lean_dec(x_9);
lean_dec(x_4);
x_2 = x_8;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BoolExpr_toString___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__9(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Std_Tactic_BVDecide_BVPred_toString(x_2);
return x_3;
}
case 1:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, 0);
lean_dec(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_mk_string_unchecked("false", 5, 5);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_mk_string_unchecked("true", 4, 4);
return x_6;
}
}
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_mk_string_unchecked("!", 1, 1);
x_9 = l_Std_Tactic_BVDecide_BoolExpr_toString___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__9(x_7);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
return x_10;
}
case 3:
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_mk_string_unchecked("(", 1, 1);
x_15 = l_Std_Tactic_BVDecide_BoolExpr_toString___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__9(x_12);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked(" ", 1, 1);
x_18 = lean_string_append(x_16, x_17);
x_19 = l_Std_Tactic_BVDecide_Gate_toString(x_11);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = lean_string_append(x_20, x_17);
lean_dec(x_17);
x_22 = l_Std_Tactic_BVDecide_BoolExpr_toString___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__9(x_13);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
x_24 = lean_mk_string_unchecked(")", 1, 1);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
return x_25;
}
default: 
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_mk_string_unchecked("(if ", 4, 4);
x_30 = l_Std_Tactic_BVDecide_BoolExpr_toString___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__9(x_26);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = lean_mk_string_unchecked(" ", 1, 1);
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Std_Tactic_BVDecide_BoolExpr_toString___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__9(x_27);
x_35 = lean_string_append(x_33, x_34);
lean_dec(x_34);
x_36 = lean_string_append(x_35, x_32);
lean_dec(x_32);
x_37 = l_Std_Tactic_BVDecide_BoolExpr_toString___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__9(x_28);
x_38 = lean_string_append(x_36, x_37);
lean_dec(x_37);
x_39 = lean_mk_string_unchecked(")", 1, 1);
x_40 = lean_string_append(x_38, x_39);
lean_dec(x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_mk_string_unchecked("Reflecting goal into BVLogicalExpr", 34, 34);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_MessageData_ofFormat(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_14 = l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
x_108 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__0___redArg(x_1, x_11, x_16);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_unbox(x_109);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; 
lean_dec(x_5);
lean_dec(x_1);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_89 = x_8;
x_90 = x_9;
x_91 = x_10;
x_92 = x_11;
x_93 = x_12;
x_94 = x_111;
goto block_107;
}
else
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_108);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_113 = lean_ctor_get(x_108, 1);
x_114 = lean_ctor_get(x_108, 0);
lean_dec(x_114);
x_115 = lean_mk_string_unchecked("Reflected bv logical expression: ", 33, 33);
x_116 = l_Lean_stringToMessageData(x_115);
lean_dec(x_115);
x_117 = lean_ctor_get(x_15, 0);
lean_inc(x_117);
x_118 = l_Std_Tactic_BVDecide_BoolExpr_toString___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__9(x_117);
x_119 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = l_Lean_MessageData_ofFormat(x_119);
lean_ctor_set_tag(x_108, 7);
lean_ctor_set(x_108, 1, x_120);
lean_ctor_set(x_108, 0, x_116);
x_121 = l_Lean_stringToMessageData(x_5);
lean_dec(x_5);
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_108);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_addTrace___at___Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg(x_1, x_122, x_9, x_10, x_11, x_12, x_113);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_89 = x_8;
x_90 = x_9;
x_91 = x_10;
x_92 = x_11;
x_93 = x_12;
x_94 = x_124;
goto block_107;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_125 = lean_ctor_get(x_108, 1);
lean_inc(x_125);
lean_dec(x_108);
x_126 = lean_mk_string_unchecked("Reflected bv logical expression: ", 33, 33);
x_127 = l_Lean_stringToMessageData(x_126);
lean_dec(x_126);
x_128 = lean_ctor_get(x_15, 0);
lean_inc(x_128);
x_129 = l_Std_Tactic_BVDecide_BoolExpr_toString___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__9(x_128);
x_130 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = l_Lean_MessageData_ofFormat(x_130);
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_stringToMessageData(x_5);
lean_dec(x_5);
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_addTrace___at___Lean_Elab_Tactic_BVDecide_Frontend_M_lookup_spec__1___redArg(x_1, x_134, x_9, x_10, x_11, x_12, x_125);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_89 = x_8;
x_90 = x_9;
x_91 = x_10;
x_92 = x_11;
x_93 = x_12;
x_94 = x_136;
goto block_107;
}
}
block_88:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_24 = lean_box(0);
x_25 = l_List_mapTR_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__4(x_23, x_24);
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
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__5___redArg(x_25, x_35);
lean_inc(x_18);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_15);
lean_inc(x_7);
x_37 = lean_apply_8(x_6, x_7, x_15, x_36, x_19, x_20, x_21, x_18, x_22);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_7);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_37, 0, x_43);
return x_37;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_dec(x_37);
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_46 = x_38;
} else {
 lean_dec_ref(x_38);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_38);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_38, 0);
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
lean_dec(x_37);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_ctor_get(x_15, 1);
lean_inc(x_54);
lean_dec(x_15);
lean_inc(x_20);
x_55 = lean_apply_7(x_54, x_52, x_17, x_19, x_20, x_21, x_18, x_51);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_MVarId_assign___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__6___redArg(x_7, x_56, x_20, x_57);
lean_dec(x_20);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
lean_ctor_set(x_38, 0, x_53);
lean_ctor_set(x_58, 0, x_38);
return x_58;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
lean_ctor_set(x_38, 0, x_53);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_38);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_53);
lean_free_object(x_38);
lean_dec(x_20);
lean_dec(x_7);
x_63 = !lean_is_exclusive(x_55);
if (x_63 == 0)
{
return x_55;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_55, 0);
x_65 = lean_ctor_get(x_55, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_55);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_38, 0);
lean_inc(x_67);
lean_dec(x_38);
x_68 = lean_ctor_get(x_37, 1);
lean_inc(x_68);
lean_dec(x_37);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_ctor_get(x_15, 1);
lean_inc(x_71);
lean_dec(x_15);
lean_inc(x_20);
x_72 = lean_apply_7(x_71, x_69, x_17, x_19, x_20, x_21, x_18, x_68);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_MVarId_assign___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__6___redArg(x_7, x_73, x_20, x_74);
lean_dec(x_20);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_70);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_70);
lean_dec(x_20);
lean_dec(x_7);
x_80 = lean_ctor_get(x_72, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_72, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_82 = x_72;
} else {
 lean_dec_ref(x_72);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_7);
x_84 = !lean_is_exclusive(x_37);
if (x_84 == 0)
{
return x_37;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_37, 0);
x_86 = lean_ctor_get(x_37, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_37);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
block_107:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_95 = lean_st_ref_get(x_89, x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_box(0);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_array_get_size(x_100);
x_102 = lean_unsigned_to_nat(0u);
x_103 = lean_nat_dec_lt(x_102, x_101);
if (x_103 == 0)
{
lean_dec(x_101);
lean_dec(x_100);
x_17 = x_89;
x_18 = x_93;
x_19 = x_90;
x_20 = x_91;
x_21 = x_92;
x_22 = x_97;
x_23 = x_99;
goto block_88;
}
else
{
size_t x_104; size_t x_105; lean_object* x_106; 
x_104 = lean_usize_of_nat(x_101);
lean_dec(x_101);
x_105 = lean_usize_of_nat(x_102);
x_106 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__8(x_100, x_104, x_105, x_99);
lean_dec(x_100);
x_17 = x_89;
x_18 = x_93;
x_19 = x_90;
x_20 = x_91;
x_21 = x_92;
x_22 = x_97;
x_23 = x_106;
goto block_88;
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_14);
if (x_137 == 0)
{
return x_14;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_14, 0);
x_139 = lean_ctor_get(x_14, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_14);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection___lam__0___boxed), 7, 0);
x_9 = lean_mk_string_unchecked("Meta", 4, 4);
x_10 = lean_mk_string_unchecked("Tactic", 6, 6);
x_11 = lean_mk_string_unchecked("bv", 2, 2);
x_12 = l_Lean_Name_mkStr3(x_9, x_10, x_11);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_reflectBV___boxed), 7, 1);
lean_closure_set(x_13, 0, x_1);
x_14 = lean_box(1);
x_15 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection___lam__1___boxed), 13, 7);
lean_closure_set(x_16, 0, x_12);
lean_closure_set(x_16, 1, x_8);
lean_closure_set(x_16, 2, x_13);
lean_closure_set(x_16, 3, x_14);
lean_closure_set(x_16, 4, x_15);
lean_closure_set(x_16, 5, x_2);
lean_closure_set(x_16, 6, x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_reflectBV_spec__2___boxed), 9, 3);
lean_closure_set(x_17, 0, lean_box(0));
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_16);
x_18 = l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg(x_17, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__2___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__0(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_assign___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__6___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_assign___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__7(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection_spec__8(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection___lam__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_mk_string_unchecked("Preparing LRAT reflection term", 30, 30);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_MessageData_ofFormat(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_11 = lean_mk_string_unchecked("Meta", 4, 4);
x_12 = lean_mk_string_unchecked("Tactic", 6, 6);
x_13 = lean_mk_string_unchecked("bv", 2, 2);
x_14 = l_Lean_Name_mkStr3(x_11, x_12, x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___boxed), 9, 4);
lean_closure_set(x_15, 0, x_3);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_4);
lean_closure_set(x_15, 3, x_5);
x_16 = lean_box(1);
x_17 = lean_mk_string_unchecked("", 0, 0);
x_18 = lean_unbox(x_16);
x_19 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_14, x_2, x_15, x_18, x_17, x_6, x_7, x_8, x_9, x_10);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat___lam__0___boxed), 6, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat___lam__1), 10, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat___lam__2___boxed), 8, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_Elab_Tactic_BVDecide_Frontend_M_run___redArg(x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvDecide_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = l_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat(x_21, x_2, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_free_object(x_10);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_22, 0, x_28);
return x_22;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_31 = x_23;
} else {
 lean_dec_ref(x_23);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 1, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_22, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_10, 0, x_37);
lean_ctor_set(x_23, 0, x_10);
return x_22;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_23, 0);
lean_inc(x_38);
lean_dec(x_23);
lean_ctor_set(x_10, 0, x_38);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_10);
lean_ctor_set(x_22, 0, x_39);
return x_22;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_dec(x_22);
x_41 = lean_ctor_get(x_23, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_42 = x_23;
} else {
 lean_dec_ref(x_23);
 x_42 = lean_box(0);
}
lean_ctor_set(x_10, 0, x_41);
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 1, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_10);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_free_object(x_10);
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
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_10, 0);
lean_inc(x_49);
lean_dec(x_10);
x_50 = l_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat(x_49, x_2, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
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
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_55 = x_51;
} else {
 lean_dec_ref(x_51);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 1, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_54);
if (lean_is_scalar(x_53)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_53;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_59 = x_50;
} else {
 lean_dec_ref(x_50);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_51, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_61 = x_51;
} else {
 lean_dec_ref(x_51);
 x_61 = lean_box(0);
}
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_60);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
if (lean_is_scalar(x_59)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_59;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_58);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_50, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_50, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_67 = x_50;
} else {
 lean_dec_ref(x_50);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_9);
if (x_69 == 0)
{
return x_9;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_9, 0);
x_71 = lean_ctor_get(x_9, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_9);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvDecide___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_explainCounterExampleQuality(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_8, x_2, x_3, x_4, x_5, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_11, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvDecide(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_bvDecide_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_bvDecide___lam__0___boxed), 6, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_13, x_12, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_3);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_8, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
return x_8;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvDecide___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_bvDecide___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_remove_file(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_io_error_to_string(x_11);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_MessageData_ofFormat(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_io_error_to_string(x_16);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_MessageData_ofFormat(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 5);
lean_inc(x_11);
x_12 = lean_io_create_tempfile(x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_16);
x_17 = lean_apply_11(x_1, x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide_spec__0___redArg___lam__0(x_16, x_11, x_20, x_19);
lean_dec(x_20);
lean_dec(x_16);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_18);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_18);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_17, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_dec(x_17);
x_32 = lean_box(0);
x_33 = l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide_spec__0___redArg___lam__0(x_16, x_11, x_32, x_31);
lean_dec(x_16);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 0, x_30);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_30);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_12);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_12, 0);
x_44 = lean_io_error_to_string(x_43);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l_Lean_MessageData_ofFormat(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_11);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_12, 0, x_47);
return x_12;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_12, 0);
x_49 = lean_ctor_get(x_12, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_12);
x_50 = lean_io_error_to_string(x_48);
x_51 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Lean_MessageData_ofFormat(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_11);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_14 = l_Lean_Elab_Tactic_BVDecide_Frontend_bvDecide(x_12, x_1, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_16, x_3, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
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
else
{
return x_17;
}
}
else
{
uint8_t x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
return x_11;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_11);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_6);
x_13 = l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new(x_3, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide___lam__0___boxed), 10, 1);
lean_closure_set(x_16, 0, x_14);
x_17 = l_Lean_Elab_Tactic_withMainContext___redArg(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = lean_mk_string_unchecked("bvDecide", 8, 8);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_15 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_14);
lean_inc(x_1);
x_16 = l_Lean_Syntax_isOfKind(x_1, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
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
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
lean_dec(x_1);
x_20 = lean_mk_string_unchecked("optConfig", 9, 9);
x_21 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_20);
lean_inc(x_19);
x_22 = l_Lean_Syntax_isOfKind(x_19, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_23;
}
else
{
lean_object* x_24; 
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(x_19, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide___lam__1___boxed), 12, 1);
lean_closure_set(x_27, 0, x_25);
x_28 = l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide_spec__0___redArg(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_withTempFile___at___Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("bvDecide", 8, 8);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_10 = lean_mk_string_unchecked("Frontend", 8, 8);
x_11 = lean_mk_string_unchecked("evalBvDecide", 12, 12);
x_12 = l_Lean_Name_mkStr6(x_3, x_8, x_5, x_9, x_10, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide), 10, 0);
x_14 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_12, x_13, x_1);
return x_14;
}
}
lean_object* initialize_Std_Sat_AIG_CNF(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_RelabelNat(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_SatAtBVLogical(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_LRAT(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_CNF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_RelabelNat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_SatAtBVLogical(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_LRAT(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_BVDecide_Frontend_explainers = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_explainers();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_explainers);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_evalBvDecide__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
