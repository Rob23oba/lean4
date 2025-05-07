// Lean compiler output
// Module: Lean.Elab.Tactic.Try
// Imports: Init.Try Init.Grind.Tactics Lean.Meta.Tactic.ExposeNames Lean.Meta.Tactic.Try Lean.Meta.Tactic.TryThis Lean.Elab.Tactic.Config Lean.Elab.Tactic.SimpTrace Lean.Elab.Tactic.LibrarySearch Lean.Elab.Tactic.Grind
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_setGrindParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacSeqElems_x3f(lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_eval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Try_Collector_OrdSet_isEmpty___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isAccessible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__12_spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_LibrarySearch_solveByElim(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_LibrarySearch_librarySearch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__1_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__10_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSuggestion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Array_reverse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestions_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__5(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeSimp_x3f(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__4(lean_object*, lean_object*, size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isAccessible___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_throwExs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__8(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_setSimpParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq_spec__0(lean_object*, size_t, size_t);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone(lean_object*);
lean_object* l_Lean_Elab_Tactic_focus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques(lean_object*);
lean_object* l_Array_mkArray2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___boxed(lean_object*);
lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__1(uint8_t, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isAccessible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_instInhabitedTSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeGrind_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_InternalExceptionId_0__Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_26_(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_focus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_eval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lam__0(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getEvalFns___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_withNonTerminal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalTryTrace___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__3_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestions_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalTryTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__2_spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getSimpParams(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_eval_suggest_tactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateTryTacticM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_throwExs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkSep(lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_merge_x3f(lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_withNonTerminal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionsCore(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go_spec__0(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getEvalFns___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Try_Collector_OrdSet_isEmpty___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_throwExs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isAccessible___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go_spec__0___redArg(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestions(lean_object*);
uint8_t l_Lean_Elab_Tactic_isSimpOnly(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalAndSuggest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_Try_Collector_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__2_spec__2(lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getEvalFns___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__5_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__7(uint8_t, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Elab_Tactic_elabGrindConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_throwExs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_withNonTerminal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalTryTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateTryTacticM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__10_spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_throwExs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getEvalFns(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkGrindOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_withNonTerminal___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_checkTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_observing___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__12_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_tryTacticElabAttribute_unsafe__1(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withExposedNames___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_tryTacticElabAttribute;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__3(uint8_t, lean_object*, lean_object*, size_t, size_t);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalGrindCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateTryTacticM;
lean_object* l_Lean_Elab_Tactic_getGrindParams(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateTryTacticM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalAndSuggest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Try___hyg_6_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Tactic_isGrindOnly(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq_spec__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateTryTacticM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_observing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_focus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toSuggestion(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr_x27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__3(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_eval_suggest_tactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpCallStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_initFn____x40_Lean_Elab_Tactic_Try___hyg_4386_(lean_object*);
lean_object* l_Lean_Expr_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTacticExceptionId;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_throwExs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at___Lean_HasConstCache_containsUnsafe_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Try___hyg_6_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Try", 3, 3);
x_9 = lean_mk_string_unchecked("Config", 6, 6);
x_10 = l_Lean_Name_mkStr3(x_7, x_8, x_9);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_Meta_evalExpr_x27(lean_box(0), x_10, x_1, x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Try___hyg_6_(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_inc(x_1);
x_37 = l_Lean_Parser_Tactic_getConfigItems(x_1);
x_38 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigItemViews(x_37);
x_39 = l_Array_isEmpty___redArg(x_38);
x_40 = lean_box(1);
if (x_39 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_st_ref_get(x_8, x_9);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = lean_ctor_get(x_7, 5);
x_46 = l_Lean_replaceRef(x_1, x_45);
lean_dec(x_1);
x_47 = lean_ctor_get(x_7, 0);
x_48 = lean_ctor_get(x_7, 1);
x_49 = lean_ctor_get(x_7, 2);
x_50 = lean_ctor_get(x_7, 3);
x_51 = lean_ctor_get(x_7, 4);
x_52 = lean_ctor_get(x_7, 6);
x_53 = lean_ctor_get(x_7, 7);
x_54 = lean_ctor_get(x_7, 8);
x_55 = lean_ctor_get(x_7, 9);
x_56 = lean_ctor_get(x_7, 10);
x_57 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_58 = lean_ctor_get(x_7, 11);
x_59 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_60 = lean_ctor_get(x_7, 12);
lean_inc(x_60);
lean_inc(x_58);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
x_61 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_61, 0, x_47);
lean_ctor_set(x_61, 1, x_48);
lean_ctor_set(x_61, 2, x_49);
lean_ctor_set(x_61, 3, x_50);
lean_ctor_set(x_61, 4, x_51);
lean_ctor_set(x_61, 5, x_46);
lean_ctor_set(x_61, 6, x_52);
lean_ctor_set(x_61, 7, x_53);
lean_ctor_set(x_61, 8, x_54);
lean_ctor_set(x_61, 9, x_55);
lean_ctor_set(x_61, 10, x_56);
lean_ctor_set(x_61, 11, x_58);
lean_ctor_set(x_61, 12, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*13, x_57);
lean_ctor_set_uint8(x_61, sizeof(void*)*13 + 1, x_59);
x_62 = lean_ctor_get(x_43, 0);
lean_inc(x_62);
lean_dec(x_43);
x_63 = lean_mk_string_unchecked("Lean", 4, 4);
x_64 = lean_mk_string_unchecked("Try", 3, 3);
x_65 = lean_mk_string_unchecked("Config", 6, 6);
x_66 = l_Lean_Name_mkStr3(x_63, x_64, x_65);
x_67 = lean_unbox(x_40);
lean_inc(x_66);
x_68 = l_Lean_Environment_contains(x_62, x_66, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec(x_38);
x_69 = lean_mk_string_unchecked("error evaluating configuration, environment does not yet contain type ", 70, 70);
x_70 = l_Lean_stringToMessageData(x_69);
lean_dec(x_69);
x_71 = l_Lean_MessageData_ofName(x_66);
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_71);
lean_ctor_set(x_41, 0, x_70);
x_72 = lean_mk_string_unchecked("", 0, 0);
x_73 = l_Lean_stringToMessageData(x_72);
lean_dec(x_72);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_41);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_74, x_3, x_4, x_5, x_6, x_61, x_8, x_44);
lean_dec(x_8);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
return x_75;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_75);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
lean_object* x_80; 
lean_free_object(x_41);
lean_inc(x_8);
lean_inc(x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_80 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(x_36, x_66, x_38, x_3, x_4, x_5, x_6, x_61, x_8, x_44);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = lean_ctor_get(x_80, 1);
x_84 = l_Lean_Expr_hasSyntheticSorry(x_82);
if (x_84 == 0)
{
uint8_t x_85; 
lean_free_object(x_80);
x_85 = l_Lean_Expr_hasSorry(x_82);
if (x_85 == 0)
{
lean_object* x_86; 
lean_inc(x_8);
lean_inc(x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_82);
x_86 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Try___hyg_6_(x_82, x_5, x_6, x_61, x_8, x_83);
if (lean_obj_tag(x_86) == 0)
{
lean_dec(x_82);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
x_89 = l_Lean_Exception_isInterrupt(x_87);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = l_Lean_Exception_isRuntime(x_87);
x_10 = x_86;
x_11 = x_8;
x_12 = x_3;
x_13 = x_6;
x_14 = x_87;
x_15 = x_4;
x_16 = x_82;
x_17 = x_88;
x_18 = x_5;
x_19 = x_61;
x_20 = x_90;
goto block_35;
}
else
{
x_10 = x_86;
x_11 = x_8;
x_12 = x_3;
x_13 = x_6;
x_14 = x_87;
x_15 = x_4;
x_16 = x_82;
x_17 = x_88;
x_18 = x_5;
x_19 = x_61;
x_20 = x_89;
goto block_35;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec(x_82);
x_91 = lean_mk_string_unchecked("configuration contains 'sorry'", 30, 30);
x_92 = l_Lean_stringToMessageData(x_91);
lean_dec(x_91);
x_93 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_92, x_3, x_4, x_5, x_6, x_61, x_8, x_83);
lean_dec(x_8);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
return x_93;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_93);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_82);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_98 = lean_unsigned_to_nat(8u);
x_99 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_84);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 1, x_84);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 2, x_39);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 3, x_39);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 4, x_84);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 5, x_39);
lean_ctor_set_uint8(x_99, sizeof(void*)*1 + 6, x_84);
lean_ctor_set(x_80, 0, x_99);
return x_80;
}
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = lean_ctor_get(x_80, 0);
x_101 = lean_ctor_get(x_80, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_80);
x_102 = l_Lean_Expr_hasSyntheticSorry(x_100);
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = l_Lean_Expr_hasSorry(x_100);
if (x_103 == 0)
{
lean_object* x_104; 
lean_inc(x_8);
lean_inc(x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_100);
x_104 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Try___hyg_6_(x_100, x_5, x_6, x_61, x_8, x_101);
if (lean_obj_tag(x_104) == 0)
{
lean_dec(x_100);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
x_107 = l_Lean_Exception_isInterrupt(x_105);
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = l_Lean_Exception_isRuntime(x_105);
x_10 = x_104;
x_11 = x_8;
x_12 = x_3;
x_13 = x_6;
x_14 = x_105;
x_15 = x_4;
x_16 = x_100;
x_17 = x_106;
x_18 = x_5;
x_19 = x_61;
x_20 = x_108;
goto block_35;
}
else
{
x_10 = x_104;
x_11 = x_8;
x_12 = x_3;
x_13 = x_6;
x_14 = x_105;
x_15 = x_4;
x_16 = x_100;
x_17 = x_106;
x_18 = x_5;
x_19 = x_61;
x_20 = x_107;
goto block_35;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_100);
x_109 = lean_mk_string_unchecked("configuration contains 'sorry'", 30, 30);
x_110 = l_Lean_stringToMessageData(x_109);
lean_dec(x_109);
x_111 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_110, x_3, x_4, x_5, x_6, x_61, x_8, x_101);
lean_dec(x_8);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_100);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_116 = lean_unsigned_to_nat(8u);
x_117 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_102);
lean_ctor_set_uint8(x_117, sizeof(void*)*1 + 1, x_102);
lean_ctor_set_uint8(x_117, sizeof(void*)*1 + 2, x_39);
lean_ctor_set_uint8(x_117, sizeof(void*)*1 + 3, x_39);
lean_ctor_set_uint8(x_117, sizeof(void*)*1 + 4, x_102);
lean_ctor_set_uint8(x_117, sizeof(void*)*1 + 5, x_39);
lean_ctor_set_uint8(x_117, sizeof(void*)*1 + 6, x_102);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_101);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_119 = !lean_is_exclusive(x_80);
if (x_119 == 0)
{
return x_80;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_80, 0);
x_121 = lean_ctor_get(x_80, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_80);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_148; 
x_123 = lean_ctor_get(x_41, 0);
x_124 = lean_ctor_get(x_41, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_41);
x_125 = lean_ctor_get(x_7, 5);
x_126 = l_Lean_replaceRef(x_1, x_125);
lean_dec(x_1);
x_127 = lean_ctor_get(x_7, 0);
x_128 = lean_ctor_get(x_7, 1);
x_129 = lean_ctor_get(x_7, 2);
x_130 = lean_ctor_get(x_7, 3);
x_131 = lean_ctor_get(x_7, 4);
x_132 = lean_ctor_get(x_7, 6);
x_133 = lean_ctor_get(x_7, 7);
x_134 = lean_ctor_get(x_7, 8);
x_135 = lean_ctor_get(x_7, 9);
x_136 = lean_ctor_get(x_7, 10);
x_137 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_138 = lean_ctor_get(x_7, 11);
x_139 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_140 = lean_ctor_get(x_7, 12);
lean_inc(x_140);
lean_inc(x_138);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
x_141 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_141, 0, x_127);
lean_ctor_set(x_141, 1, x_128);
lean_ctor_set(x_141, 2, x_129);
lean_ctor_set(x_141, 3, x_130);
lean_ctor_set(x_141, 4, x_131);
lean_ctor_set(x_141, 5, x_126);
lean_ctor_set(x_141, 6, x_132);
lean_ctor_set(x_141, 7, x_133);
lean_ctor_set(x_141, 8, x_134);
lean_ctor_set(x_141, 9, x_135);
lean_ctor_set(x_141, 10, x_136);
lean_ctor_set(x_141, 11, x_138);
lean_ctor_set(x_141, 12, x_140);
lean_ctor_set_uint8(x_141, sizeof(void*)*13, x_137);
lean_ctor_set_uint8(x_141, sizeof(void*)*13 + 1, x_139);
x_142 = lean_ctor_get(x_123, 0);
lean_inc(x_142);
lean_dec(x_123);
x_143 = lean_mk_string_unchecked("Lean", 4, 4);
x_144 = lean_mk_string_unchecked("Try", 3, 3);
x_145 = lean_mk_string_unchecked("Config", 6, 6);
x_146 = l_Lean_Name_mkStr3(x_143, x_144, x_145);
x_147 = lean_unbox(x_40);
lean_inc(x_146);
x_148 = l_Lean_Environment_contains(x_142, x_146, x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_38);
x_149 = lean_mk_string_unchecked("error evaluating configuration, environment does not yet contain type ", 70, 70);
x_150 = l_Lean_stringToMessageData(x_149);
lean_dec(x_149);
x_151 = l_Lean_MessageData_ofName(x_146);
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_mk_string_unchecked("", 0, 0);
x_154 = l_Lean_stringToMessageData(x_153);
lean_dec(x_153);
x_155 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_155, x_3, x_4, x_5, x_6, x_141, x_8, x_124);
lean_dec(x_8);
lean_dec(x_141);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
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
else
{
lean_object* x_161; 
lean_inc(x_8);
lean_inc(x_141);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_161 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(x_36, x_146, x_38, x_3, x_4, x_5, x_6, x_141, x_8, x_124);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_164 = x_161;
} else {
 lean_dec_ref(x_161);
 x_164 = lean_box(0);
}
x_165 = l_Lean_Expr_hasSyntheticSorry(x_162);
if (x_165 == 0)
{
uint8_t x_166; 
lean_dec(x_164);
x_166 = l_Lean_Expr_hasSorry(x_162);
if (x_166 == 0)
{
lean_object* x_167; 
lean_inc(x_8);
lean_inc(x_141);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_162);
x_167 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Try___hyg_6_(x_162, x_5, x_6, x_141, x_8, x_163);
if (lean_obj_tag(x_167) == 0)
{
lean_dec(x_162);
lean_dec(x_141);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
x_170 = l_Lean_Exception_isInterrupt(x_168);
if (x_170 == 0)
{
uint8_t x_171; 
x_171 = l_Lean_Exception_isRuntime(x_168);
x_10 = x_167;
x_11 = x_8;
x_12 = x_3;
x_13 = x_6;
x_14 = x_168;
x_15 = x_4;
x_16 = x_162;
x_17 = x_169;
x_18 = x_5;
x_19 = x_141;
x_20 = x_171;
goto block_35;
}
else
{
x_10 = x_167;
x_11 = x_8;
x_12 = x_3;
x_13 = x_6;
x_14 = x_168;
x_15 = x_4;
x_16 = x_162;
x_17 = x_169;
x_18 = x_5;
x_19 = x_141;
x_20 = x_170;
goto block_35;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_162);
x_172 = lean_mk_string_unchecked("configuration contains 'sorry'", 30, 30);
x_173 = l_Lean_stringToMessageData(x_172);
lean_dec(x_172);
x_174 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_173, x_3, x_4, x_5, x_6, x_141, x_8, x_163);
lean_dec(x_8);
lean_dec(x_141);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_162);
lean_dec(x_141);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_179 = lean_unsigned_to_nat(8u);
x_180 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set_uint8(x_180, sizeof(void*)*1, x_165);
lean_ctor_set_uint8(x_180, sizeof(void*)*1 + 1, x_165);
lean_ctor_set_uint8(x_180, sizeof(void*)*1 + 2, x_39);
lean_ctor_set_uint8(x_180, sizeof(void*)*1 + 3, x_39);
lean_ctor_set_uint8(x_180, sizeof(void*)*1 + 4, x_165);
lean_ctor_set_uint8(x_180, sizeof(void*)*1 + 5, x_39);
lean_ctor_set_uint8(x_180, sizeof(void*)*1 + 6, x_165);
if (lean_is_scalar(x_164)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_164;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_163);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_141);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_182 = lean_ctor_get(x_161, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_161, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_184 = x_161;
} else {
 lean_dec_ref(x_161);
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
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; uint8_t x_190; uint8_t x_191; uint8_t x_192; uint8_t x_193; uint8_t x_194; uint8_t x_195; lean_object* x_196; 
lean_dec(x_38);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_186 = lean_box(0);
x_187 = lean_unsigned_to_nat(8u);
x_188 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_188, 0, x_187);
x_189 = lean_unbox(x_40);
lean_ctor_set_uint8(x_188, sizeof(void*)*1, x_189);
x_190 = lean_unbox(x_40);
lean_ctor_set_uint8(x_188, sizeof(void*)*1 + 1, x_190);
x_191 = lean_unbox(x_186);
lean_ctor_set_uint8(x_188, sizeof(void*)*1 + 2, x_191);
x_192 = lean_unbox(x_186);
lean_ctor_set_uint8(x_188, sizeof(void*)*1 + 3, x_192);
x_193 = lean_unbox(x_40);
lean_ctor_set_uint8(x_188, sizeof(void*)*1 + 4, x_193);
x_194 = lean_unbox(x_186);
lean_ctor_set_uint8(x_188, sizeof(void*)*1 + 5, x_194);
x_195 = lean_unbox(x_40);
lean_ctor_set_uint8(x_188, sizeof(void*)*1 + 6, x_195);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_188);
lean_ctor_set(x_196, 1, x_9);
return x_196;
}
block_35:
{
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_10);
x_21 = lean_mk_string_unchecked("error evaluating configuration\n", 31, 31);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = l_Lean_MessageData_ofExpr(x_16);
x_24 = l_Lean_indentD(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked("\n\nException: ", 13, 13);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Exception_toMessageData(x_14);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked("", 0, 0);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_33, x_12, x_15, x_18, x_13, x_19, x_11, x_17);
lean_dec(x_11);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_18);
lean_dec(x_15);
return x_34;
}
else
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabTryConfig___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_elabTryConfig___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabTryConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isAccessible___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_2);
x_6 = l_Lean_FVarId_getDecl___redArg(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_16; lean_object* x_19; lean_object* x_30; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
x_30 = lean_ctor_get(x_7, 2);
lean_inc(x_30);
x_19 = x_30;
goto block_29;
block_15:
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
x_13 = lean_box(x_12);
if (lean_is_scalar(x_9)) {
 x_14 = lean_alloc_ctor(0, 2, 0);
} else {
 x_14 = x_9;
}
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
block_18:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_10 = x_16;
x_11 = x_17;
goto block_15;
}
block_29:
{
uint8_t x_20; 
x_20 = l_Lean_Name_hasMacroScopes(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
lean_dec(x_2);
x_22 = l_Lean_LocalContext_findFromUserName_x3f(x_21, x_19);
lean_dec(x_19);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
lean_dec(x_7);
x_23 = lean_box(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_8);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_16 = x_26;
goto block_18;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
return x_28;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_6);
if (x_31 == 0)
{
return x_6;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_6, 0);
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_6);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isAccessible(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isAccessible___redArg(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isAccessible___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isAccessible___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isAccessible___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isAccessible(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_18; lean_object* x_19; 
x_9 = lean_box(1);
x_18 = lean_array_uget(x_1, x_2);
lean_inc(x_4);
x_19 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isAccessible___redArg(x_18, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
lean_ctor_set(x_19, 0, x_9);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_10 = x_8;
x_11 = x_26;
goto block_17;
}
}
else
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_unbox(x_27);
lean_dec(x_27);
x_10 = x_29;
x_11 = x_28;
goto block_17;
}
else
{
lean_dec(x_4);
return x_19;
}
}
block_17:
{
if (x_10 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_7 = x_11;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_7);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
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
x_24 = lean_st_mk_ref(x_23, x_6);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Expr_collectFVars(x_1, x_25, x_2, x_3, x_4, x_5, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_st_ref_get(x_25, x_28);
lean_dec(x_25);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 2);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_array_get_size(x_32);
x_34 = lean_nat_dec_lt(x_12, x_33);
if (x_34 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_2);
x_7 = x_31;
goto block_10;
}
else
{
if (x_34 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_2);
x_7 = x_31;
goto block_10;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; 
x_35 = lean_usize_of_nat(x_12);
x_36 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_37 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible_spec__0___redArg(x_32, x_35, x_36, x_2, x_4, x_5, x_31);
lean_dec(x_32);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_7 = x_40;
goto block_10;
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_37, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_37, 0, x_43);
return x_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_dec(x_37);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
return x_37;
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible_spec__0___redArg(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible_spec__0(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_checkTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = l_Lean_Elab_Tactic_saveState___redArg(x_4, x_6, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_Elab_Tactic_SavedState_restore(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Elab_Tactic_evalTactic(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unbox(x_15);
x_23 = l_Lean_Elab_Tactic_SavedState_restore(x_13, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_20);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_unbox(x_15);
x_31 = l_Lean_Elab_Tactic_SavedState_restore(x_13, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_unsigned_to_nat(6u);
x_10 = l_Lean_Meta_LibrarySearch_solveByElim(x_8, x_1, x_2, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
x_9 = l_Lean_PrettyPrinter_delab(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_st_ref_get(x_7, x_12);
lean_dec(x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_6, 5);
lean_inc(x_16);
lean_dec(x_6);
x_17 = l_Lean_SourceInfo_fromRef(x_16, x_3);
lean_dec(x_16);
x_18 = lean_mk_string_unchecked("Lean", 4, 4);
x_19 = lean_mk_string_unchecked("Parser", 6, 6);
x_20 = lean_mk_string_unchecked("Tactic", 6, 6);
x_21 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_22 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_21);
x_23 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_17);
lean_ctor_set_tag(x_9, 2);
lean_ctor_set(x_9, 1, x_23);
lean_ctor_set(x_9, 0, x_17);
x_24 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_25 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_24);
x_26 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_27 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_26);
x_28 = lean_mk_string_unchecked("null", 4, 4);
x_29 = l_Lean_Name_mkStr1(x_28);
x_30 = lean_mk_string_unchecked("exposeNames", 11, 11);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_31 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_30);
x_32 = lean_mk_string_unchecked("expose_names", 12, 12);
lean_inc(x_17);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_17);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_17);
x_34 = l_Lean_Syntax_node1(x_17, x_31, x_33);
x_35 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_17);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_37);
x_38 = l_Lean_Name_mkStr4(x_18, x_19, x_20, x_37);
lean_inc(x_17);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_17);
lean_ctor_set(x_39, 1, x_37);
lean_inc(x_17);
x_40 = l_Lean_Syntax_node2(x_17, x_38, x_39, x_11);
lean_inc(x_17);
x_41 = l_Lean_Syntax_node3(x_17, x_29, x_34, x_36, x_40);
lean_inc(x_17);
x_42 = l_Lean_Syntax_node1(x_17, x_27, x_41);
lean_inc(x_17);
x_43 = l_Lean_Syntax_node1(x_17, x_25, x_42);
x_44 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_17);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_17);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Syntax_node3(x_17, x_22, x_9, x_43, x_45);
lean_ctor_set(x_13, 0, x_46);
return x_13;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_47 = lean_ctor_get(x_13, 1);
lean_inc(x_47);
lean_dec(x_13);
x_48 = lean_ctor_get(x_6, 5);
lean_inc(x_48);
lean_dec(x_6);
x_49 = l_Lean_SourceInfo_fromRef(x_48, x_3);
lean_dec(x_48);
x_50 = lean_mk_string_unchecked("Lean", 4, 4);
x_51 = lean_mk_string_unchecked("Parser", 6, 6);
x_52 = lean_mk_string_unchecked("Tactic", 6, 6);
x_53 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_54 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_53);
x_55 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_49);
lean_ctor_set_tag(x_9, 2);
lean_ctor_set(x_9, 1, x_55);
lean_ctor_set(x_9, 0, x_49);
x_56 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_57 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_56);
x_58 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_59 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_58);
x_60 = lean_mk_string_unchecked("null", 4, 4);
x_61 = l_Lean_Name_mkStr1(x_60);
x_62 = lean_mk_string_unchecked("exposeNames", 11, 11);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
x_63 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_62);
x_64 = lean_mk_string_unchecked("expose_names", 12, 12);
lean_inc(x_49);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_49);
lean_ctor_set(x_65, 1, x_64);
lean_inc(x_49);
x_66 = l_Lean_Syntax_node1(x_49, x_63, x_65);
x_67 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_49);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_49);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_69);
x_70 = l_Lean_Name_mkStr4(x_50, x_51, x_52, x_69);
lean_inc(x_49);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_49);
lean_ctor_set(x_71, 1, x_69);
lean_inc(x_49);
x_72 = l_Lean_Syntax_node2(x_49, x_70, x_71, x_11);
lean_inc(x_49);
x_73 = l_Lean_Syntax_node3(x_49, x_61, x_66, x_68, x_72);
lean_inc(x_49);
x_74 = l_Lean_Syntax_node1(x_49, x_59, x_73);
lean_inc(x_49);
x_75 = l_Lean_Syntax_node1(x_49, x_57, x_74);
x_76 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_49);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_49);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Syntax_node3(x_49, x_54, x_9, x_75, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_47);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_80 = lean_ctor_get(x_9, 0);
x_81 = lean_ctor_get(x_9, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_9);
x_82 = lean_st_ref_get(x_7, x_81);
lean_dec(x_7);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_6, 5);
lean_inc(x_85);
lean_dec(x_6);
x_86 = l_Lean_SourceInfo_fromRef(x_85, x_3);
lean_dec(x_85);
x_87 = lean_mk_string_unchecked("Lean", 4, 4);
x_88 = lean_mk_string_unchecked("Parser", 6, 6);
x_89 = lean_mk_string_unchecked("Tactic", 6, 6);
x_90 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
x_91 = l_Lean_Name_mkStr4(x_87, x_88, x_89, x_90);
x_92 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_86);
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_86);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
x_95 = l_Lean_Name_mkStr4(x_87, x_88, x_89, x_94);
x_96 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
x_97 = l_Lean_Name_mkStr4(x_87, x_88, x_89, x_96);
x_98 = lean_mk_string_unchecked("null", 4, 4);
x_99 = l_Lean_Name_mkStr1(x_98);
x_100 = lean_mk_string_unchecked("exposeNames", 11, 11);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
x_101 = l_Lean_Name_mkStr4(x_87, x_88, x_89, x_100);
x_102 = lean_mk_string_unchecked("expose_names", 12, 12);
lean_inc(x_86);
x_103 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_103, 0, x_86);
lean_ctor_set(x_103, 1, x_102);
lean_inc(x_86);
x_104 = l_Lean_Syntax_node1(x_86, x_101, x_103);
x_105 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_86);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_86);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_107);
x_108 = l_Lean_Name_mkStr4(x_87, x_88, x_89, x_107);
lean_inc(x_86);
x_109 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_109, 0, x_86);
lean_ctor_set(x_109, 1, x_107);
lean_inc(x_86);
x_110 = l_Lean_Syntax_node2(x_86, x_108, x_109, x_80);
lean_inc(x_86);
x_111 = l_Lean_Syntax_node3(x_86, x_99, x_104, x_106, x_110);
lean_inc(x_86);
x_112 = l_Lean_Syntax_node1(x_86, x_97, x_111);
lean_inc(x_86);
x_113 = l_Lean_Syntax_node1(x_86, x_95, x_112);
x_114 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_86);
x_115 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_115, 0, x_86);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_Syntax_node3(x_86, x_91, x_93, x_113, x_115);
if (lean_is_scalar(x_84)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_84;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_83);
return x_117;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_38; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_38 = l_Lean_Meta_LibrarySearch_librarySearch(x_1, x_2, x_3, x_4, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Expr_mvar___override(x_1);
x_42 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_41, x_12, x_40);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Expr_headBeta(x_43);
lean_inc(x_11);
lean_inc(x_45);
x_46 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible(x_45, x_11, x_12, x_13, x_14, x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_box(0);
x_51 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_evalSuggestExact___lam__2___boxed), 8, 3);
lean_closure_set(x_51, 0, x_45);
lean_closure_set(x_51, 1, x_50);
lean_closure_set(x_51, 2, x_47);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_52 = l_Lean_Meta_withExposedNames___redArg(x_51, x_11, x_12, x_13, x_14, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_16 = x_53;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = x_54;
goto block_37;
}
else
{
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
return x_52;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_47);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_dec(x_46);
x_56 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_57 = l_Lean_PrettyPrinter_delab(x_45, x_56, x_11, x_12, x_13, x_14, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_st_ref_get(x_14, x_59);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_62 = lean_ctor_get(x_60, 1);
x_63 = lean_ctor_get(x_60, 0);
lean_dec(x_63);
x_64 = lean_ctor_get(x_13, 5);
lean_inc(x_64);
x_65 = lean_box(0);
x_66 = lean_unbox(x_65);
x_67 = l_Lean_SourceInfo_fromRef(x_64, x_66);
lean_dec(x_64);
x_68 = lean_mk_string_unchecked("Lean", 4, 4);
x_69 = lean_mk_string_unchecked("Parser", 6, 6);
x_70 = lean_mk_string_unchecked("Tactic", 6, 6);
x_71 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_71);
x_72 = l_Lean_Name_mkStr4(x_68, x_69, x_70, x_71);
lean_inc(x_67);
lean_ctor_set_tag(x_60, 2);
lean_ctor_set(x_60, 1, x_71);
lean_ctor_set(x_60, 0, x_67);
x_73 = l_Lean_Syntax_node2(x_67, x_72, x_60, x_58);
x_16 = x_73;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = x_62;
goto block_37;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_74 = lean_ctor_get(x_60, 1);
lean_inc(x_74);
lean_dec(x_60);
x_75 = lean_ctor_get(x_13, 5);
lean_inc(x_75);
x_76 = lean_box(0);
x_77 = lean_unbox(x_76);
x_78 = l_Lean_SourceInfo_fromRef(x_75, x_77);
lean_dec(x_75);
x_79 = lean_mk_string_unchecked("Lean", 4, 4);
x_80 = lean_mk_string_unchecked("Parser", 6, 6);
x_81 = lean_mk_string_unchecked("Tactic", 6, 6);
x_82 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_82);
x_83 = l_Lean_Name_mkStr4(x_79, x_80, x_81, x_82);
lean_inc(x_78);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_Lean_Syntax_node2(x_78, x_83, x_84, x_58);
x_16 = x_85;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = x_13;
x_24 = x_14;
x_25 = x_74;
goto block_37;
}
}
else
{
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
return x_57;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_45);
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
x_86 = !lean_is_exclusive(x_46);
if (x_86 == 0)
{
return x_46;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_46, 0);
x_88 = lean_ctor_get(x_46, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_46);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_39);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_90 = lean_ctor_get(x_38, 1);
lean_inc(x_90);
lean_dec(x_38);
x_91 = lean_mk_string_unchecked("`exact\?` failed", 15, 15);
x_92 = l_Lean_stringToMessageData(x_91);
lean_dec(x_91);
x_93 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_92, x_11, x_12, x_13, x_14, x_90);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_93;
}
}
else
{
uint8_t x_94; 
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
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_38);
if (x_94 == 0)
{
return x_38;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_38, 0);
x_96 = lean_ctor_get(x_38, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_38);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
block_37:
{
lean_object* x_26; 
lean_inc(x_18);
lean_inc(x_16);
x_26 = l_Lean_Elab_Tactic_Try_checkTactic(x_5, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Elab_Tactic_setGoals___redArg(x_6, x_18, x_27);
lean_dec(x_18);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_16);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_6);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_Elab_Tactic_saveState___redArg(x_2, x_4, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Tactic_getGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_mk_string_unchecked("no goals", 8, 8);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
x_18 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_17, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_evalSuggestExact___lam__0___boxed), 7, 0);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_evalSuggestExact___lam__1___boxed), 6, 0);
x_24 = lean_unsigned_to_nat(10u);
lean_inc(x_20);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_evalSuggestExact___lam__3), 15, 6);
lean_closure_set(x_25, 0, x_20);
lean_closure_set(x_25, 1, x_22);
lean_closure_set(x_25, 2, x_23);
lean_closure_set(x_25, 3, x_24);
lean_closure_set(x_25, 4, x_11);
lean_closure_set(x_25, 5, x_21);
x_26 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(x_20, x_25, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lam__0(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lam__2(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_Try_evalSuggestExact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("tryResult", 9, 9);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = lean_array_push(x_9, x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_13 = l_Lean_Syntax_getArgs(x_12);
lean_dec(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSuggestion(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic(x_2);
x_4 = l_Array_append(lean_box(0), x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Array_isEmpty___redArg(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_5, x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_4, 5);
x_15 = l_Lean_SourceInfo_fromRef(x_14, x_10);
x_16 = lean_mk_string_unchecked("Lean", 4, 4);
x_17 = lean_mk_string_unchecked("Parser", 6, 6);
x_18 = lean_mk_string_unchecked("Tactic", 6, 6);
x_19 = lean_mk_string_unchecked("tryResult", 9, 9);
x_20 = l_Lean_Name_mkStr4(x_16, x_17, x_18, x_19);
x_21 = lean_mk_string_unchecked("try_suggestions", 15, 15);
lean_inc(x_15);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_mk_string_unchecked("null", 4, 4);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = l_Array_mkArray0(lean_box(0));
x_26 = l_Array_append(lean_box(0), x_25, x_1);
lean_inc(x_15);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_26);
x_28 = l_Lean_Syntax_node2(x_15, x_20, x_22, x_27);
lean_ctor_set(x_11, 0, x_28);
return x_11;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_dec(x_11);
x_30 = lean_ctor_get(x_4, 5);
x_31 = l_Lean_SourceInfo_fromRef(x_30, x_10);
x_32 = lean_mk_string_unchecked("Lean", 4, 4);
x_33 = lean_mk_string_unchecked("Parser", 6, 6);
x_34 = lean_mk_string_unchecked("Tactic", 6, 6);
x_35 = lean_mk_string_unchecked("tryResult", 9, 9);
x_36 = l_Lean_Name_mkStr4(x_32, x_33, x_34, x_35);
x_37 = lean_mk_string_unchecked("try_suggestions", 15, 15);
lean_inc(x_31);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_mk_string_unchecked("null", 4, 4);
x_40 = l_Lean_Name_mkStr1(x_39);
x_41 = l_Array_mkArray0(lean_box(0));
x_42 = l_Array_append(lean_box(0), x_41, x_1);
lean_inc(x_31);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_31);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_42);
x_44 = l_Lean_Syntax_node2(x_31, x_36, x_38, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_29);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_mk_string_unchecked("tactic", 6, 6);
x_47 = l_Lean_Name_mkStr1(x_46);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_instInhabitedTSyntax(x_49);
lean_dec(x_49);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_array_get(x_50, x_1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_6);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_mk_string_unchecked("`mkTrySuggestions` failed", 25, 25);
x_55 = l_Lean_stringToMessageData(x_54);
lean_dec(x_54);
x_56 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_55, x_2, x_3, x_4, x_5, x_6);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg(x_1, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_mk_string_unchecked("Lean", 4, 4);
x_14 = lean_mk_string_unchecked("Parser", 6, 6);
x_15 = lean_mk_string_unchecked("Tactic", 6, 6);
x_16 = lean_mk_string_unchecked("done", 4, 4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_17 = l_Lean_Name_mkStr4(x_13, x_14, x_15, x_16);
lean_inc(x_12);
x_18 = l_Lean_Syntax_isOfKind(x_12, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_mk_string_unchecked("skip", 4, 4);
x_20 = l_Lean_Name_mkStr4(x_13, x_14, x_15, x_19);
lean_inc(x_12);
x_21 = l_Lean_Syntax_isOfKind(x_12, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_array_push(x_4, x_12);
x_5 = x_22;
goto block_10;
}
else
{
lean_dec(x_12);
x_5 = x_4;
goto block_10;
}
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_5 = x_4;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_array_get_size(x_1);
x_4 = lean_mk_empty_array_with_capacity(x_2);
x_5 = lean_nat_dec_lt(x_2, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_2);
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone_spec__0(x_1, x_7, x_8, x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacSeqElems_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
x_11 = lean_mk_string_unchecked("tacticSeqBracketed", 18, 18);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_11);
lean_inc(x_10);
x_13 = l_Lean_Syntax_isOfKind(x_10, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
x_15 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_14);
lean_inc(x_10);
x_16 = l_Lean_Syntax_isOfKind(x_10, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_10);
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = l_Lean_Syntax_getArg(x_10, x_9);
lean_dec(x_10);
x_19 = l_Lean_Syntax_getArgs(x_18);
lean_dec(x_18);
x_20 = l_Lean_Syntax_TSepArray_getElems___redArg(x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Syntax_getArg(x_10, x_22);
lean_dec(x_10);
x_24 = l_Lean_Syntax_getArgs(x_23);
lean_dec(x_23);
x_25 = l_Lean_Syntax_TSepArray_getElems___redArg(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("cdot", 4, 4);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = lean_mk_string_unchecked("cdotTk", 6, 6);
lean_inc(x_2);
x_9 = l_Lean_Name_mkStr2(x_2, x_8);
x_10 = l_Lean_Syntax_isOfKind(x_7, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_13 = lean_mk_string_unchecked("Parser", 6, 6);
x_14 = lean_mk_string_unchecked("Tactic", 6, 6);
x_15 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_16 = l_Lean_Name_mkStr4(x_2, x_13, x_14, x_15);
x_17 = l_Lean_Syntax_isOfKind(x_12, x_16);
lean_dec(x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac(x_5);
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
return x_6;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
lean_inc(x_2);
x_8 = l_Lean_Syntax_isOfKind(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_mk_string_unchecked("cdot", 4, 4);
lean_inc(x_3);
x_10 = l_Lean_Name_mkStr2(x_3, x_9);
lean_inc(x_2);
x_11 = l_Lean_Syntax_isOfKind(x_2, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_array_push(x_1, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_2, x_13);
x_15 = lean_mk_string_unchecked("cdotTk", 6, 6);
lean_inc(x_3);
x_16 = l_Lean_Name_mkStr2(x_3, x_15);
x_17 = l_Lean_Syntax_isOfKind(x_14, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_array_push(x_1, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_2, x_19);
x_21 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_22 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_21);
lean_inc(x_20);
x_23 = l_Lean_Syntax_isOfKind(x_20, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_20);
x_24 = lean_array_push(x_1, x_2);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacSeqElems_x3f(x_20);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_array_push(x_1, x_2);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; uint8_t x_32; lean_object* x_34; uint8_t x_35; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_34 = lean_array_get_size(x_27);
x_35 = lean_nat_dec_lt(x_13, x_34);
if (x_35 == 0)
{
lean_dec(x_34);
x_32 = x_8;
goto block_33;
}
else
{
if (x_35 == 0)
{
lean_dec(x_34);
x_32 = x_8;
goto block_33;
}
else
{
size_t x_36; size_t x_37; uint8_t x_38; 
x_36 = lean_usize_of_nat(x_13);
x_37 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_38 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq_spec__0(x_27, x_36, x_37);
x_32 = x_38;
goto block_33;
}
}
block_31:
{
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_27);
x_29 = lean_array_push(x_1, x_2);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_2);
x_30 = l_Array_append(lean_box(0), x_1, x_27);
lean_dec(x_27);
return x_30;
}
}
block_33:
{
if (x_32 == 0)
{
x_28 = x_23;
goto block_31;
}
else
{
x_28 = x_8;
goto block_31;
}
}
}
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = lean_unsigned_to_nat(1u);
x_40 = l_Lean_Syntax_getArg(x_2, x_39);
x_41 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_42 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_41);
lean_inc(x_40);
x_43 = l_Lean_Syntax_isOfKind(x_40, x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_40);
x_44 = lean_array_push(x_1, x_2);
return x_44;
}
else
{
lean_object* x_45; 
x_45 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacSeqElems_x3f(x_40);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_array_push(x_1, x_2);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_2);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Array_append(lean_box(0), x_1, x_47);
lean_dec(x_47);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq_spec__0(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone(x_1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_eq(x_7, x_10);
lean_dec(x_7);
if (x_11 == 0)
{
if (x_2 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_st_ref_get(x_4, x_5);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_3, 5);
x_16 = l_Lean_SourceInfo_fromRef(x_15, x_2);
x_17 = lean_mk_string_unchecked("tactic", 6, 6);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked("Lean", 4, 4);
x_22 = lean_mk_string_unchecked("Parser", 6, 6);
x_23 = lean_mk_string_unchecked("Tactic", 6, 6);
x_24 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_25 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_24);
x_26 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_16);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_29 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_28);
x_30 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
x_31 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_30);
x_32 = lean_mk_string_unchecked("null", 4, 4);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = l_Array_mkArray0(lean_box(0));
x_35 = lean_mk_string_unchecked(";", 1, 1);
x_36 = l_Lean_Syntax_TSepArray_ofElems(x_20, x_35, x_6);
lean_dec(x_6);
lean_dec(x_20);
x_37 = l_Array_append(lean_box(0), x_34, x_36);
lean_dec(x_36);
lean_inc(x_16);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_16);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_37);
lean_inc(x_16);
x_39 = l_Lean_Syntax_node1(x_16, x_31, x_38);
lean_inc(x_16);
x_40 = l_Lean_Syntax_node1(x_16, x_29, x_39);
x_41 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_16);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_16);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Syntax_node3(x_16, x_25, x_27, x_40, x_42);
lean_ctor_set(x_12, 0, x_43);
return x_12;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_44 = lean_ctor_get(x_12, 1);
lean_inc(x_44);
lean_dec(x_12);
x_45 = lean_ctor_get(x_3, 5);
x_46 = l_Lean_SourceInfo_fromRef(x_45, x_2);
x_47 = lean_mk_string_unchecked("tactic", 6, 6);
x_48 = l_Lean_Name_mkStr1(x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_mk_string_unchecked("Lean", 4, 4);
x_52 = lean_mk_string_unchecked("Parser", 6, 6);
x_53 = lean_mk_string_unchecked("Tactic", 6, 6);
x_54 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_55 = l_Lean_Name_mkStr4(x_51, x_52, x_53, x_54);
x_56 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_46);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_46);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_59 = l_Lean_Name_mkStr4(x_51, x_52, x_53, x_58);
x_60 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
x_61 = l_Lean_Name_mkStr4(x_51, x_52, x_53, x_60);
x_62 = lean_mk_string_unchecked("null", 4, 4);
x_63 = l_Lean_Name_mkStr1(x_62);
x_64 = l_Array_mkArray0(lean_box(0));
x_65 = lean_mk_string_unchecked(";", 1, 1);
x_66 = l_Lean_Syntax_TSepArray_ofElems(x_50, x_65, x_6);
lean_dec(x_6);
lean_dec(x_50);
x_67 = l_Array_append(lean_box(0), x_64, x_66);
lean_dec(x_66);
lean_inc(x_46);
x_68 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_68, 0, x_46);
lean_ctor_set(x_68, 1, x_63);
lean_ctor_set(x_68, 2, x_67);
lean_inc(x_46);
x_69 = l_Lean_Syntax_node1(x_46, x_61, x_68);
lean_inc(x_46);
x_70 = l_Lean_Syntax_node1(x_46, x_59, x_69);
x_71 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_46);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_46);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_Syntax_node3(x_46, x_55, x_57, x_70, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_44);
return x_74;
}
}
else
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_st_ref_get(x_4, x_5);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_77 = lean_ctor_get(x_75, 0);
lean_dec(x_77);
x_78 = lean_ctor_get(x_3, 5);
x_79 = l_Lean_SourceInfo_fromRef(x_78, x_11);
x_80 = lean_mk_string_unchecked("tactic", 6, 6);
x_81 = l_Lean_Name_mkStr1(x_80);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_mk_string_unchecked("Lean", 4, 4);
x_85 = lean_mk_string_unchecked("cdot", 4, 4);
lean_inc(x_84);
x_86 = l_Lean_Name_mkStr2(x_84, x_85);
x_87 = lean_mk_string_unchecked("cdotTk", 6, 6);
lean_inc(x_84);
x_88 = l_Lean_Name_mkStr2(x_84, x_87);
x_89 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_90 = l_Lean_Name_mkStr1(x_89);
x_91 = lean_mk_string_unchecked("token", 5, 5);
x_92 = lean_mk_string_unchecked("· ", 3, 2);
x_93 = l_Lean_Name_mkStr2(x_91, x_92);
x_94 = lean_mk_string_unchecked("·", 2, 1);
lean_inc(x_79);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_79);
lean_ctor_set(x_95, 1, x_94);
lean_inc(x_79);
x_96 = l_Lean_Syntax_node1(x_79, x_93, x_95);
lean_inc(x_79);
x_97 = l_Lean_Syntax_node1(x_79, x_90, x_96);
lean_inc(x_79);
x_98 = l_Lean_Syntax_node1(x_79, x_88, x_97);
x_99 = lean_mk_string_unchecked("Parser", 6, 6);
x_100 = lean_mk_string_unchecked("Tactic", 6, 6);
x_101 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_84);
x_102 = l_Lean_Name_mkStr4(x_84, x_99, x_100, x_101);
x_103 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
x_104 = l_Lean_Name_mkStr4(x_84, x_99, x_100, x_103);
x_105 = lean_mk_string_unchecked("null", 4, 4);
x_106 = l_Lean_Name_mkStr1(x_105);
x_107 = l_Array_mkArray0(lean_box(0));
x_108 = lean_mk_string_unchecked(";", 1, 1);
x_109 = l_Lean_Syntax_TSepArray_ofElems(x_83, x_108, x_6);
lean_dec(x_6);
lean_dec(x_83);
x_110 = l_Array_append(lean_box(0), x_107, x_109);
lean_dec(x_109);
lean_inc(x_79);
x_111 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_111, 0, x_79);
lean_ctor_set(x_111, 1, x_106);
lean_ctor_set(x_111, 2, x_110);
lean_inc(x_79);
x_112 = l_Lean_Syntax_node1(x_79, x_104, x_111);
lean_inc(x_79);
x_113 = l_Lean_Syntax_node1(x_79, x_102, x_112);
x_114 = l_Lean_Syntax_node2(x_79, x_86, x_98, x_113);
lean_ctor_set(x_75, 0, x_114);
return x_75;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_115 = lean_ctor_get(x_75, 1);
lean_inc(x_115);
lean_dec(x_75);
x_116 = lean_ctor_get(x_3, 5);
x_117 = l_Lean_SourceInfo_fromRef(x_116, x_11);
x_118 = lean_mk_string_unchecked("tactic", 6, 6);
x_119 = l_Lean_Name_mkStr1(x_118);
x_120 = lean_box(0);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_mk_string_unchecked("Lean", 4, 4);
x_123 = lean_mk_string_unchecked("cdot", 4, 4);
lean_inc(x_122);
x_124 = l_Lean_Name_mkStr2(x_122, x_123);
x_125 = lean_mk_string_unchecked("cdotTk", 6, 6);
lean_inc(x_122);
x_126 = l_Lean_Name_mkStr2(x_122, x_125);
x_127 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_128 = l_Lean_Name_mkStr1(x_127);
x_129 = lean_mk_string_unchecked("token", 5, 5);
x_130 = lean_mk_string_unchecked("· ", 3, 2);
x_131 = l_Lean_Name_mkStr2(x_129, x_130);
x_132 = lean_mk_string_unchecked("·", 2, 1);
lean_inc(x_117);
x_133 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_133, 0, x_117);
lean_ctor_set(x_133, 1, x_132);
lean_inc(x_117);
x_134 = l_Lean_Syntax_node1(x_117, x_131, x_133);
lean_inc(x_117);
x_135 = l_Lean_Syntax_node1(x_117, x_128, x_134);
lean_inc(x_117);
x_136 = l_Lean_Syntax_node1(x_117, x_126, x_135);
x_137 = lean_mk_string_unchecked("Parser", 6, 6);
x_138 = lean_mk_string_unchecked("Tactic", 6, 6);
x_139 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_122);
x_140 = l_Lean_Name_mkStr4(x_122, x_137, x_138, x_139);
x_141 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
x_142 = l_Lean_Name_mkStr4(x_122, x_137, x_138, x_141);
x_143 = lean_mk_string_unchecked("null", 4, 4);
x_144 = l_Lean_Name_mkStr1(x_143);
x_145 = l_Array_mkArray0(lean_box(0));
x_146 = lean_mk_string_unchecked(";", 1, 1);
x_147 = l_Lean_Syntax_TSepArray_ofElems(x_121, x_146, x_6);
lean_dec(x_6);
lean_dec(x_121);
x_148 = l_Array_append(lean_box(0), x_145, x_147);
lean_dec(x_147);
lean_inc(x_117);
x_149 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_149, 0, x_117);
lean_ctor_set(x_149, 1, x_144);
lean_ctor_set(x_149, 2, x_148);
lean_inc(x_117);
x_150 = l_Lean_Syntax_node1(x_117, x_142, x_149);
lean_inc(x_117);
x_151 = l_Lean_Syntax_node1(x_117, x_140, x_150);
x_152 = l_Lean_Syntax_node2(x_117, x_124, x_136, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_115);
return x_153;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_154 = lean_mk_string_unchecked("tactic", 6, 6);
x_155 = l_Lean_Name_mkStr1(x_154);
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Lean_instInhabitedTSyntax(x_157);
lean_dec(x_157);
x_159 = lean_array_get(x_158, x_6, x_8);
lean_dec(x_6);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_5);
return x_160;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
if (x_2 == 0)
{
lean_object* x_161; uint8_t x_162; 
x_161 = lean_st_ref_get(x_4, x_5);
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_163 = lean_ctor_get(x_161, 0);
lean_dec(x_163);
x_164 = lean_ctor_get(x_3, 5);
x_165 = l_Lean_SourceInfo_fromRef(x_164, x_2);
x_166 = lean_mk_string_unchecked("Lean", 4, 4);
x_167 = lean_mk_string_unchecked("Parser", 6, 6);
x_168 = lean_mk_string_unchecked("Tactic", 6, 6);
x_169 = lean_mk_string_unchecked("skip", 4, 4);
lean_inc(x_169);
x_170 = l_Lean_Name_mkStr4(x_166, x_167, x_168, x_169);
lean_inc(x_165);
x_171 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_171, 0, x_165);
lean_ctor_set(x_171, 1, x_169);
x_172 = l_Lean_Syntax_node1(x_165, x_170, x_171);
lean_ctor_set(x_161, 0, x_172);
return x_161;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_173 = lean_ctor_get(x_161, 1);
lean_inc(x_173);
lean_dec(x_161);
x_174 = lean_ctor_get(x_3, 5);
x_175 = l_Lean_SourceInfo_fromRef(x_174, x_2);
x_176 = lean_mk_string_unchecked("Lean", 4, 4);
x_177 = lean_mk_string_unchecked("Parser", 6, 6);
x_178 = lean_mk_string_unchecked("Tactic", 6, 6);
x_179 = lean_mk_string_unchecked("skip", 4, 4);
lean_inc(x_179);
x_180 = l_Lean_Name_mkStr4(x_176, x_177, x_178, x_179);
lean_inc(x_175);
x_181 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_181, 0, x_175);
lean_ctor_set(x_181, 1, x_179);
x_182 = l_Lean_Syntax_node1(x_175, x_180, x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_173);
return x_183;
}
}
else
{
lean_object* x_184; uint8_t x_185; 
x_184 = lean_st_ref_get(x_4, x_5);
x_185 = !lean_is_exclusive(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_186 = lean_ctor_get(x_184, 0);
lean_dec(x_186);
x_187 = lean_ctor_get(x_3, 5);
x_188 = lean_box(0);
x_189 = lean_unbox(x_188);
x_190 = l_Lean_SourceInfo_fromRef(x_187, x_189);
x_191 = lean_mk_string_unchecked("Lean", 4, 4);
x_192 = lean_mk_string_unchecked("Parser", 6, 6);
x_193 = lean_mk_string_unchecked("Tactic", 6, 6);
x_194 = lean_mk_string_unchecked("done", 4, 4);
lean_inc(x_194);
x_195 = l_Lean_Name_mkStr4(x_191, x_192, x_193, x_194);
lean_inc(x_190);
x_196 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_196, 0, x_190);
lean_ctor_set(x_196, 1, x_194);
x_197 = l_Lean_Syntax_node1(x_190, x_195, x_196);
lean_ctor_set(x_184, 0, x_197);
return x_184;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_198 = lean_ctor_get(x_184, 1);
lean_inc(x_198);
lean_dec(x_184);
x_199 = lean_ctor_get(x_3, 5);
x_200 = lean_box(0);
x_201 = lean_unbox(x_200);
x_202 = l_Lean_SourceInfo_fromRef(x_199, x_201);
x_203 = lean_mk_string_unchecked("Lean", 4, 4);
x_204 = lean_mk_string_unchecked("Parser", 6, 6);
x_205 = lean_mk_string_unchecked("Tactic", 6, 6);
x_206 = lean_mk_string_unchecked("done", 4, 4);
lean_inc(x_206);
x_207 = l_Lean_Name_mkStr4(x_203, x_204, x_205, x_206);
lean_inc(x_202);
x_208 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_208, 0, x_202);
lean_ctor_set(x_208, 1, x_206);
x_209 = l_Lean_Syntax_node1(x_202, x_207, x_208);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_198);
return x_210;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("tacticSorry", 11, 11);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_mk_string_unchecked("Lean", 4, 4);
x_14 = lean_mk_string_unchecked("Parser", 6, 6);
x_15 = lean_mk_string_unchecked("Tactic", 6, 6);
x_16 = lean_mk_string_unchecked("tacticSorry", 11, 11);
x_17 = l_Lean_Name_mkStr4(x_13, x_14, x_15, x_16);
lean_inc(x_12);
x_18 = l_Lean_Syntax_isOfKind(x_12, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_array_push(x_4, x_12);
x_5 = x_19;
goto block_10;
}
else
{
lean_dec(x_12);
x_5 = x_4;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_array_get_size(x_1);
x_4 = lean_mk_empty_array_with_capacity(x_2);
x_5 = lean_nat_dec_lt(x_2, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_2);
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry_spec__0(x_1, x_7, x_8, x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = l_Lean_Syntax_structEq(x_1, x_6);
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
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = lean_usize_of_nat(x_3);
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at___Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__0_spec__0(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__2_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
return x_4;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_1, x_3);
lean_inc(x_12);
x_13 = l_Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__0(x_4, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_array_push(x_4, x_12);
x_5 = x_14;
goto block_10;
}
else
{
lean_dec(x_12);
x_5 = x_4;
goto block_10;
}
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
return x_4;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_1, x_3);
lean_inc(x_12);
x_13 = l_Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__0(x_4, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_array_push(x_4, x_12);
x_5 = x_14;
goto block_10;
}
else
{
lean_dec(x_12);
x_5 = x_4;
goto block_10;
}
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_3, x_7);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__2_spec__2(x_1, x_2, x_8, x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_array_size(x_1);
x_5 = lean_usize_of_nat(x_2);
x_6 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__2(x_1, x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__0_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__0(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__2_spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionsCore(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic(x_1);
x_3 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry(x_2);
lean_dec(x_2);
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_box(1);
x_8 = lean_array_uget(x_3, x_4);
lean_inc(x_1);
x_9 = l_Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__0(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_1);
x_10 = lean_unbox(x_7);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = l_Array_isEmpty___redArg(x_2);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_4, x_13);
x_4 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = lean_unbox(x_7);
return x_16;
}
}
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_box(1);
x_8 = lean_array_uget(x_3, x_4);
lean_inc(x_1);
x_9 = l_Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__0(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_1);
x_10 = lean_unbox(x_7);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = l_Array_isEmpty___redArg(x_2);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; uint8_t x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_4, x_13);
x_15 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__0_spec__0(x_1, x_2, x_3, x_14, x_5);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = lean_unbox(x_7);
return x_16;
}
}
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__2_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_array_uget(x_2, x_4);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_array_get_size(x_1);
lean_inc(x_1);
x_18 = l_Array_toSubarray___redArg(x_1, x_16, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 2);
lean_inc(x_20);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
goto block_15;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_30; uint8_t x_31; 
x_22 = l_Array_isEmpty___redArg(x_1);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_30 = lean_array_get_size(x_23);
x_31 = lean_nat_dec_le(x_20, x_30);
if (x_31 == 0)
{
lean_dec(x_20);
x_24 = x_30;
goto block_29;
}
else
{
lean_dec(x_30);
x_24 = x_20;
goto block_29;
}
block_29:
{
uint8_t x_25; 
x_25 = lean_nat_dec_lt(x_19, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
goto block_15;
}
else
{
size_t x_26; size_t x_27; uint8_t x_28; 
x_26 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_27 = lean_usize_of_nat(x_24);
lean_dec(x_24);
lean_inc(x_13);
x_28 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__0(x_13, x_1, x_23, x_26, x_27);
lean_dec(x_23);
if (x_28 == 0)
{
goto block_15;
}
else
{
if (x_22 == 0)
{
lean_dec(x_13);
x_6 = x_5;
goto block_11;
}
else
{
goto block_15;
}
}
}
}
}
block_15:
{
lean_object* x_14; 
x_14 = lean_array_push(x_5, x_13);
x_6 = x_14;
goto block_11;
}
}
block_11:
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_array_uget(x_2, x_4);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_array_get_size(x_1);
lean_inc(x_1);
x_18 = l_Array_toSubarray___redArg(x_1, x_16, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 2);
lean_inc(x_20);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
goto block_15;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_30; uint8_t x_31; 
x_22 = l_Array_isEmpty___redArg(x_1);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_30 = lean_array_get_size(x_23);
x_31 = lean_nat_dec_le(x_20, x_30);
if (x_31 == 0)
{
lean_dec(x_20);
x_24 = x_30;
goto block_29;
}
else
{
lean_dec(x_30);
x_24 = x_20;
goto block_29;
}
block_29:
{
uint8_t x_25; 
x_25 = lean_nat_dec_lt(x_19, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
goto block_15;
}
else
{
size_t x_26; size_t x_27; uint8_t x_28; 
x_26 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_27 = lean_usize_of_nat(x_24);
lean_dec(x_24);
lean_inc(x_13);
x_28 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__0(x_13, x_1, x_23, x_26, x_27);
lean_dec(x_23);
if (x_28 == 0)
{
goto block_15;
}
else
{
if (x_22 == 0)
{
lean_dec(x_13);
x_6 = x_5;
goto block_11;
}
else
{
goto block_15;
}
}
}
}
}
block_15:
{
lean_object* x_14; 
x_14 = lean_array_push(x_5, x_13);
x_6 = x_14;
goto block_11;
}
}
block_11:
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_4, x_8);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__2_spec__2(x_1, x_2, x_3, x_9, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Array_isEmpty___redArg(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = l_Array_instInhabited(lean_box(0));
x_6 = lean_array_get(x_5, x_1, x_3);
x_7 = lean_array_size(x_6);
x_8 = lean_usize_of_nat(x_3);
x_9 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__2(x_1, x_6, x_7, x_8, x_4);
lean_dec(x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__0_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__2_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_2, x_3);
lean_inc(x_13);
x_14 = l_Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__0(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_array_push(x_5, x_13);
x_6 = x_15;
goto block_11;
}
else
{
lean_dec(x_13);
x_6 = x_5;
goto block_11;
}
}
else
{
return x_5;
}
block_11:
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_2, x_3);
lean_inc(x_13);
x_14 = l_Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates_spec__0(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_array_push(x_5, x_13);
x_6 = x_15;
goto block_11;
}
else
{
lean_dec(x_13);
x_6 = x_5;
goto block_11;
}
}
else
{
return x_5;
}
block_11:
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_3, x_8);
x_10 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__0_spec__0(x_1, x_2, x_9, x_4, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__2_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_6);
x_18 = lean_mk_empty_array_with_capacity(x_16);
x_19 = lean_nat_dec_lt(x_16, x_17);
if (x_19 == 0)
{
lean_dec(x_17);
lean_dec(x_6);
x_9 = x_18;
goto block_15;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_17, x_17);
if (x_20 == 0)
{
lean_dec(x_17);
lean_dec(x_6);
x_9 = x_18;
goto block_15;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = lean_usize_of_nat(x_16);
x_22 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_23 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__0(x_1, x_6, x_21, x_22, x_18);
lean_dec(x_6);
x_9 = x_23;
goto block_15;
}
}
block_15:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_6);
x_18 = lean_mk_empty_array_with_capacity(x_16);
x_19 = lean_nat_dec_lt(x_16, x_17);
if (x_19 == 0)
{
lean_dec(x_17);
lean_dec(x_6);
x_9 = x_18;
goto block_15;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_17, x_17);
if (x_20 == 0)
{
lean_dec(x_17);
lean_dec(x_6);
x_9 = x_18;
goto block_15;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = lean_usize_of_nat(x_16);
x_22 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_23 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__0(x_1, x_6, x_21, x_22, x_18);
lean_dec(x_6);
x_9 = x_23;
goto block_15;
}
}
block_15:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_8, x_3, x_9);
x_14 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__2_spec__2(x_1, x_2, x_12, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_array_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__2(x_2, x_3, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__0_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__2_spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs_spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Syntax_getKind(x_6);
x_8 = lean_name_eq(x_7, x_1);
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
return x_8;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
return x_14;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_box(1);
x_9 = lean_array_uget(x_3, x_4);
x_10 = lean_array_get_size(x_9);
x_11 = lean_nat_dec_lt(x_7, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_10);
lean_dec(x_9);
x_12 = lean_unbox(x_8);
return x_12;
}
else
{
if (x_11 == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_9);
x_13 = lean_unbox(x_8);
return x_13;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = lean_usize_of_nat(x_7);
x_15 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_16 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__0(x_1, x_9, x_14, x_15);
lean_dec(x_9);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = lean_unbox(x_8);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = l_Array_isEmpty___redArg(x_2);
if (x_18 == 0)
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
x_23 = lean_unbox(x_8);
return x_23;
}
}
}
}
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
return x_25;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_box(1);
x_9 = lean_array_uget(x_3, x_4);
x_10 = lean_array_get_size(x_9);
x_11 = lean_nat_dec_lt(x_7, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_10);
lean_dec(x_9);
x_12 = lean_unbox(x_8);
return x_12;
}
else
{
if (x_11 == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_9);
x_13 = lean_unbox(x_8);
return x_13;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = lean_usize_of_nat(x_7);
x_15 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_16 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__0(x_1, x_9, x_14, x_15);
lean_dec(x_9);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = lean_unbox(x_8);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = l_Array_isEmpty___redArg(x_2);
if (x_18 == 0)
{
lean_object* x_19; size_t x_20; size_t x_21; uint8_t x_22; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_add(x_4, x_20);
x_22 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__1_spec__1(x_1, x_2, x_3, x_21, x_5);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_unbox(x_8);
return x_23;
}
}
}
}
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__3_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_18; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_13 = l_Array_isEmpty___redArg(x_1);
x_14 = lean_array_uget(x_2, x_4);
x_15 = l_Lean_Syntax_getKind(x_14);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_array_get_size(x_1);
lean_inc(x_1);
x_22 = l_Array_toSubarray___redArg(x_1, x_20, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 2);
lean_inc(x_24);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_18 = x_13;
goto block_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_33; uint8_t x_34; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_33 = lean_array_get_size(x_26);
x_34 = lean_nat_dec_le(x_24, x_33);
if (x_34 == 0)
{
lean_dec(x_24);
x_27 = x_33;
goto block_32;
}
else
{
lean_dec(x_33);
x_27 = x_24;
goto block_32;
}
block_32:
{
uint8_t x_28; 
x_28 = lean_nat_dec_lt(x_23, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_23);
x_18 = x_13;
goto block_19;
}
else
{
size_t x_29; size_t x_30; uint8_t x_31; 
x_29 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_30 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_31 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__1(x_15, x_1, x_26, x_29, x_30);
lean_dec(x_26);
x_18 = x_31;
goto block_19;
}
}
}
block_17:
{
lean_object* x_16; 
x_16 = lean_array_push(x_5, x_15);
x_6 = x_16;
goto block_11;
}
block_19:
{
if (x_18 == 0)
{
goto block_17;
}
else
{
if (x_13 == 0)
{
lean_dec(x_15);
x_6 = x_5;
goto block_11;
}
else
{
goto block_17;
}
}
}
}
block_11:
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_18; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_13 = l_Array_isEmpty___redArg(x_1);
x_14 = lean_array_uget(x_2, x_4);
x_15 = l_Lean_Syntax_getKind(x_14);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_array_get_size(x_1);
lean_inc(x_1);
x_22 = l_Array_toSubarray___redArg(x_1, x_20, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 2);
lean_inc(x_24);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_18 = x_13;
goto block_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_33; uint8_t x_34; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_33 = lean_array_get_size(x_26);
x_34 = lean_nat_dec_le(x_24, x_33);
if (x_34 == 0)
{
lean_dec(x_24);
x_27 = x_33;
goto block_32;
}
else
{
lean_dec(x_33);
x_27 = x_24;
goto block_32;
}
block_32:
{
uint8_t x_28; 
x_28 = lean_nat_dec_lt(x_23, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_23);
x_18 = x_13;
goto block_19;
}
else
{
size_t x_29; size_t x_30; uint8_t x_31; 
x_29 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_30 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_31 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__1(x_15, x_1, x_26, x_29, x_30);
lean_dec(x_26);
x_18 = x_31;
goto block_19;
}
}
}
block_17:
{
lean_object* x_16; 
x_16 = lean_array_push(x_5, x_15);
x_6 = x_16;
goto block_11;
}
block_19:
{
if (x_18 == 0)
{
goto block_17;
}
else
{
if (x_13 == 0)
{
lean_dec(x_15);
x_6 = x_5;
goto block_11;
}
else
{
goto block_17;
}
}
}
}
block_11:
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_4, x_8);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__3_spec__3(x_1, x_2, x_3, x_9, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Array_isEmpty___redArg(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = l_Array_instInhabited(lean_box(0));
x_6 = lean_array_get(x_5, x_1, x_3);
x_7 = lean_array_size(x_6);
x_8 = lean_usize_of_nat(x_3);
x_9 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__3(x_1, x_6, x_7, x_8, x_4);
lean_dec(x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__1_spec__1(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__1(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__3_spec__3(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll_spec__3(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_List_beq___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_name_eq(x_9, x_11);
if (x_13 == 0)
{
return x_13;
}
else
{
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_getGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_Elab_Tactic_evalTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Elab_Tactic_getGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = l_List_beq___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic_spec__0(x_13, x_19);
lean_dec(x_19);
lean_dec(x_13);
if (x_21 == 0)
{
lean_free_object(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_ctor_set(x_17, 0, x_1);
return x_17;
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_free_object(x_17);
lean_dec(x_1);
x_22 = lean_st_ref_get(x_9, x_20);
lean_dec(x_9);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_8, 5);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_box(0);
x_27 = lean_unbox(x_26);
x_28 = l_Lean_SourceInfo_fromRef(x_25, x_27);
lean_dec(x_25);
x_29 = lean_mk_string_unchecked("Lean", 4, 4);
x_30 = lean_mk_string_unchecked("Parser", 6, 6);
x_31 = lean_mk_string_unchecked("Tactic", 6, 6);
x_32 = lean_mk_string_unchecked("skip", 4, 4);
lean_inc(x_32);
x_33 = l_Lean_Name_mkStr4(x_29, x_30, x_31, x_32);
lean_inc(x_28);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_32);
lean_ctor_set(x_11, 0, x_28);
x_34 = l_Lean_Syntax_node1(x_28, x_33, x_11);
lean_ctor_set(x_22, 0, x_34);
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_dec(x_22);
x_36 = lean_ctor_get(x_8, 5);
lean_inc(x_36);
lean_dec(x_8);
x_37 = lean_box(0);
x_38 = lean_unbox(x_37);
x_39 = l_Lean_SourceInfo_fromRef(x_36, x_38);
lean_dec(x_36);
x_40 = lean_mk_string_unchecked("Lean", 4, 4);
x_41 = lean_mk_string_unchecked("Parser", 6, 6);
x_42 = lean_mk_string_unchecked("Tactic", 6, 6);
x_43 = lean_mk_string_unchecked("skip", 4, 4);
lean_inc(x_43);
x_44 = l_Lean_Name_mkStr4(x_40, x_41, x_42, x_43);
lean_inc(x_39);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_43);
lean_ctor_set(x_11, 0, x_39);
x_45 = l_Lean_Syntax_node1(x_39, x_44, x_11);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_35);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_17, 0);
x_48 = lean_ctor_get(x_17, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_17);
x_49 = l_List_beq___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic_spec__0(x_13, x_47);
lean_dec(x_47);
lean_dec(x_13);
if (x_49 == 0)
{
lean_object* x_50; 
lean_free_object(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_1);
x_51 = lean_st_ref_get(x_9, x_48);
lean_dec(x_9);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_8, 5);
lean_inc(x_54);
lean_dec(x_8);
x_55 = lean_box(0);
x_56 = lean_unbox(x_55);
x_57 = l_Lean_SourceInfo_fromRef(x_54, x_56);
lean_dec(x_54);
x_58 = lean_mk_string_unchecked("Lean", 4, 4);
x_59 = lean_mk_string_unchecked("Parser", 6, 6);
x_60 = lean_mk_string_unchecked("Tactic", 6, 6);
x_61 = lean_mk_string_unchecked("skip", 4, 4);
lean_inc(x_61);
x_62 = l_Lean_Name_mkStr4(x_58, x_59, x_60, x_61);
lean_inc(x_57);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_61);
lean_ctor_set(x_11, 0, x_57);
x_63 = l_Lean_Syntax_node1(x_57, x_62, x_11);
if (lean_is_scalar(x_53)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_53;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_52);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_15);
if (x_65 == 0)
{
return x_15;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_15, 0);
x_67 = lean_ctor_get(x_15, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_15);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_11, 0);
x_70 = lean_ctor_get(x_11, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_71 = l_Lean_Elab_Tactic_evalTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l_Lean_Elab_Tactic_getGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_72);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
x_77 = l_List_beq___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic_spec__0(x_69, x_74);
lean_dec(x_74);
lean_dec(x_69);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_9);
lean_dec(x_8);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_76);
lean_dec(x_1);
x_79 = lean_st_ref_get(x_9, x_75);
lean_dec(x_9);
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
x_82 = lean_ctor_get(x_8, 5);
lean_inc(x_82);
lean_dec(x_8);
x_83 = lean_box(0);
x_84 = lean_unbox(x_83);
x_85 = l_Lean_SourceInfo_fromRef(x_82, x_84);
lean_dec(x_82);
x_86 = lean_mk_string_unchecked("Lean", 4, 4);
x_87 = lean_mk_string_unchecked("Parser", 6, 6);
x_88 = lean_mk_string_unchecked("Tactic", 6, 6);
x_89 = lean_mk_string_unchecked("skip", 4, 4);
lean_inc(x_89);
x_90 = l_Lean_Name_mkStr4(x_86, x_87, x_88, x_89);
lean_inc(x_85);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_85);
lean_ctor_set(x_91, 1, x_89);
x_92 = l_Lean_Syntax_node1(x_85, x_90, x_91);
if (lean_is_scalar(x_81)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_81;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_80);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_69);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_ctor_get(x_71, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_71, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_96 = x_71;
} else {
 lean_dec_ref(x_71);
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
}
}
LEAN_EXPORT lean_object* l_List_beq___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("Tactic", 6, 6);
x_8 = lean_mk_string_unchecked("grindTrace", 10, 10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_8);
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_66 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_67 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_66);
lean_inc(x_13);
x_68 = l_Lean_Syntax_isOfKind(x_13, x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_112; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_112 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_4);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_142; uint8_t x_143; 
x_113 = lean_unsigned_to_nat(2u);
x_142 = l_Lean_Syntax_getArg(x_1, x_113);
x_143 = l_Lean_Syntax_isNone(x_142);
if (x_143 == 0)
{
uint8_t x_144; 
lean_inc(x_142);
x_144 = l_Lean_Syntax_matchesNull(x_142, x_12);
if (x_144 == 0)
{
lean_object* x_145; 
lean_dec(x_142);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_145 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_4);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_unsigned_to_nat(0u);
x_147 = l_Lean_Syntax_getArg(x_142, x_146);
lean_dec(x_142);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_128 = x_148;
x_129 = x_2;
x_130 = x_3;
x_131 = x_4;
goto block_141;
}
}
else
{
lean_object* x_149; 
lean_dec(x_142);
x_149 = lean_box(0);
x_128 = x_149;
x_129 = x_2;
x_130 = x_3;
x_131 = x_4;
goto block_141;
}
block_127:
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = lean_unsigned_to_nat(4u);
x_120 = l_Lean_Syntax_getArg(x_1, x_119);
lean_dec(x_1);
x_121 = l_Lean_Syntax_isNone(x_120);
if (x_121 == 0)
{
uint8_t x_122; 
lean_inc(x_120);
x_122 = l_Lean_Syntax_matchesNull(x_120, x_113);
if (x_122 == 0)
{
lean_object* x_123; 
lean_dec(x_120);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_123 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_118);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = l_Lean_Syntax_getArg(x_120, x_12);
lean_dec(x_120);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_69 = x_115;
x_70 = x_114;
x_71 = x_125;
x_72 = x_116;
x_73 = x_117;
x_74 = x_118;
goto block_111;
}
}
else
{
lean_object* x_126; 
lean_dec(x_120);
x_126 = lean_box(0);
x_69 = x_115;
x_70 = x_114;
x_71 = x_126;
x_72 = x_116;
x_73 = x_117;
x_74 = x_118;
goto block_111;
}
}
block_141:
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_unsigned_to_nat(3u);
x_133 = l_Lean_Syntax_getArg(x_1, x_132);
x_134 = l_Lean_Syntax_isNone(x_133);
if (x_134 == 0)
{
uint8_t x_135; 
lean_inc(x_133);
x_135 = l_Lean_Syntax_matchesNull(x_133, x_132);
if (x_135 == 0)
{
lean_object* x_136; 
lean_dec(x_133);
lean_dec(x_128);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_136 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_131);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = l_Lean_Syntax_getArg(x_133, x_12);
lean_dec(x_133);
x_138 = l_Lean_Syntax_getArgs(x_137);
lean_dec(x_137);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_114 = x_128;
x_115 = x_139;
x_116 = x_129;
x_117 = x_130;
x_118 = x_131;
goto block_127;
}
}
else
{
lean_object* x_140; 
lean_dec(x_133);
x_140 = lean_box(0);
x_114 = x_128;
x_115 = x_140;
x_116 = x_129;
x_117 = x_130;
x_118 = x_131;
goto block_127;
}
}
}
block_27:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = l_Array_append(lean_box(0), x_15, x_22);
lean_dec(x_22);
lean_inc(x_18);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_23);
x_25 = l_Lean_Syntax_node5(x_18, x_19, x_14, x_13, x_17, x_16, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
block_44:
{
lean_object* x_37; lean_object* x_38; 
lean_inc(x_29);
x_37 = l_Array_append(lean_box(0), x_29, x_36);
lean_dec(x_36);
lean_inc(x_34);
lean_inc(x_31);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_37);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_39; 
x_39 = l_Array_empty(lean_box(0));
x_14 = x_28;
x_15 = x_29;
x_16 = x_38;
x_17 = x_30;
x_18 = x_31;
x_19 = x_33;
x_20 = x_34;
x_21 = x_35;
x_22 = x_39;
goto block_27;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_mk_string_unchecked("on_failure", 10, 10);
lean_inc(x_31);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Array_mkArray2(lean_box(0), x_42, x_40);
x_14 = x_28;
x_15 = x_29;
x_16 = x_38;
x_17 = x_30;
x_18 = x_31;
x_19 = x_33;
x_20 = x_34;
x_21 = x_35;
x_22 = x_43;
goto block_27;
}
}
block_65:
{
lean_object* x_54; lean_object* x_55; 
lean_inc(x_47);
x_54 = l_Array_append(lean_box(0), x_47, x_53);
lean_dec(x_53);
lean_inc(x_51);
lean_inc(x_48);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_51);
lean_ctor_set(x_55, 2, x_54);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_56; 
x_56 = l_Array_empty(lean_box(0));
x_28 = x_46;
x_29 = x_47;
x_30 = x_55;
x_31 = x_48;
x_32 = x_49;
x_33 = x_50;
x_34 = x_51;
x_35 = x_52;
x_36 = x_56;
goto block_44;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_45, 0);
lean_inc(x_57);
lean_dec(x_45);
x_58 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_48);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_48);
lean_ctor_set(x_59, 1, x_58);
lean_inc(x_47);
x_60 = l_Array_append(lean_box(0), x_47, x_57);
lean_dec(x_57);
lean_inc(x_51);
lean_inc(x_48);
x_61 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_61, 0, x_48);
lean_ctor_set(x_61, 1, x_51);
lean_ctor_set(x_61, 2, x_60);
x_62 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_48);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_48);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Array_mkArray3(lean_box(0), x_59, x_61, x_63);
x_28 = x_46;
x_29 = x_47;
x_30 = x_55;
x_31 = x_48;
x_32 = x_49;
x_33 = x_50;
x_34 = x_51;
x_35 = x_52;
x_36 = x_64;
goto block_44;
}
}
block_111:
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_st_ref_get(x_73, x_74);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_77 = lean_ctor_get(x_75, 1);
x_78 = lean_ctor_get(x_75, 0);
lean_dec(x_78);
x_79 = lean_ctor_get(x_72, 5);
x_80 = lean_box(0);
x_81 = lean_unbox(x_80);
x_82 = l_Lean_SourceInfo_fromRef(x_79, x_81);
x_83 = lean_mk_string_unchecked("grind", 5, 5);
lean_inc(x_83);
x_84 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_83);
lean_inc(x_82);
lean_ctor_set_tag(x_75, 2);
lean_ctor_set(x_75, 1, x_83);
lean_ctor_set(x_75, 0, x_82);
x_85 = lean_mk_string_unchecked("null", 4, 4);
x_86 = l_Lean_Name_mkStr1(x_85);
x_87 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_88; 
x_88 = l_Array_empty(lean_box(0));
x_45 = x_69;
x_46 = x_75;
x_47 = x_87;
x_48 = x_82;
x_49 = x_71;
x_50 = x_84;
x_51 = x_86;
x_52 = x_77;
x_53 = x_88;
goto block_65;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_70, 0);
lean_inc(x_89);
lean_dec(x_70);
x_90 = l_Lean_SourceInfo_fromRef(x_89, x_68);
lean_dec(x_89);
x_91 = lean_mk_string_unchecked("only", 4, 4);
x_92 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Array_mkArray1___redArg(x_92);
x_45 = x_69;
x_46 = x_75;
x_47 = x_87;
x_48 = x_82;
x_49 = x_71;
x_50 = x_84;
x_51 = x_86;
x_52 = x_77;
x_53 = x_93;
goto block_65;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_94 = lean_ctor_get(x_75, 1);
lean_inc(x_94);
lean_dec(x_75);
x_95 = lean_ctor_get(x_72, 5);
x_96 = lean_box(0);
x_97 = lean_unbox(x_96);
x_98 = l_Lean_SourceInfo_fromRef(x_95, x_97);
x_99 = lean_mk_string_unchecked("grind", 5, 5);
lean_inc(x_99);
x_100 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_99);
lean_inc(x_98);
x_101 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
x_102 = lean_mk_string_unchecked("null", 4, 4);
x_103 = l_Lean_Name_mkStr1(x_102);
x_104 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_105; 
x_105 = l_Array_empty(lean_box(0));
x_45 = x_69;
x_46 = x_101;
x_47 = x_104;
x_48 = x_98;
x_49 = x_71;
x_50 = x_100;
x_51 = x_103;
x_52 = x_94;
x_53 = x_105;
goto block_65;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_70, 0);
lean_inc(x_106);
lean_dec(x_70);
x_107 = l_Lean_SourceInfo_fromRef(x_106, x_68);
lean_dec(x_106);
x_108 = lean_mk_string_unchecked("only", 4, 4);
x_109 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Array_mkArray1___redArg(x_109);
x_45 = x_69;
x_46 = x_101;
x_47 = x_104;
x_48 = x_98;
x_49 = x_71;
x_50 = x_100;
x_51 = x_103;
x_52 = x_94;
x_53 = x_110;
goto block_65;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___redArg(x_1, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("Tactic", 6, 6);
x_8 = lean_mk_string_unchecked("simpTrace", 9, 9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_8);
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_matchesNull(x_14, x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_unsigned_to_nat(2u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_19 = lean_mk_string_unchecked("simpTraceArgsRest", 17, 17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_19);
lean_inc(x_18);
x_21 = l_Lean_Syntax_isOfKind(x_18, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_4);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_23 = l_Lean_Syntax_getArg(x_18, x_12);
x_78 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_79 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_78);
lean_inc(x_23);
x_80 = l_Lean_Syntax_isOfKind(x_23, x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_81 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_4);
return x_81;
}
else
{
lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_82 = l_Lean_Syntax_getArg(x_18, x_13);
x_83 = l_Lean_Syntax_matchesNull(x_82, x_12);
if (x_83 == 0)
{
lean_object* x_161; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_161 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_4);
return x_161;
}
else
{
lean_object* x_162; uint8_t x_163; 
x_162 = l_Lean_Syntax_getArg(x_18, x_17);
x_163 = l_Lean_Syntax_isNone(x_162);
if (x_163 == 0)
{
uint8_t x_164; 
lean_inc(x_162);
x_164 = l_Lean_Syntax_matchesNull(x_162, x_13);
if (x_164 == 0)
{
lean_object* x_165; 
lean_dec(x_162);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_165 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_4);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = l_Lean_Syntax_getArg(x_162, x_12);
lean_dec(x_162);
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_166);
x_142 = x_167;
x_143 = x_2;
x_144 = x_3;
x_145 = x_4;
goto block_160;
}
}
else
{
lean_object* x_168; 
lean_dec(x_162);
x_168 = lean_box(0);
x_142 = x_168;
x_143 = x_2;
x_144 = x_3;
x_145 = x_4;
goto block_160;
}
}
block_128:
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_st_ref_get(x_85, x_87);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_92 = lean_ctor_get(x_90, 1);
x_93 = lean_ctor_get(x_90, 0);
lean_dec(x_93);
x_94 = lean_ctor_get(x_84, 5);
x_95 = lean_box(0);
x_96 = lean_unbox(x_95);
x_97 = l_Lean_SourceInfo_fromRef(x_94, x_96);
x_98 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_98);
x_99 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_98);
lean_inc(x_97);
lean_ctor_set_tag(x_90, 2);
lean_ctor_set(x_90, 1, x_98);
lean_ctor_set(x_90, 0, x_97);
x_100 = lean_mk_string_unchecked("null", 4, 4);
x_101 = l_Lean_Name_mkStr1(x_100);
x_102 = l_Array_mkArray0(lean_box(0));
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_97);
x_103 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_103, 0, x_97);
lean_ctor_set(x_103, 1, x_101);
lean_ctor_set(x_103, 2, x_102);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_104; 
x_104 = l_Array_empty(lean_box(0));
x_56 = x_89;
x_57 = x_97;
x_58 = x_90;
x_59 = x_102;
x_60 = x_101;
x_61 = x_103;
x_62 = x_88;
x_63 = x_92;
x_64 = x_99;
x_65 = x_104;
goto block_77;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_ctor_get(x_86, 0);
lean_inc(x_105);
lean_dec(x_86);
x_106 = l_Lean_SourceInfo_fromRef(x_105, x_83);
lean_dec(x_105);
x_107 = lean_mk_string_unchecked("only", 4, 4);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Array_mkArray1___redArg(x_108);
x_56 = x_89;
x_57 = x_97;
x_58 = x_90;
x_59 = x_102;
x_60 = x_101;
x_61 = x_103;
x_62 = x_88;
x_63 = x_92;
x_64 = x_99;
x_65 = x_109;
goto block_77;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_110 = lean_ctor_get(x_90, 1);
lean_inc(x_110);
lean_dec(x_90);
x_111 = lean_ctor_get(x_84, 5);
x_112 = lean_box(0);
x_113 = lean_unbox(x_112);
x_114 = l_Lean_SourceInfo_fromRef(x_111, x_113);
x_115 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_115);
x_116 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_115);
lean_inc(x_114);
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
x_118 = lean_mk_string_unchecked("null", 4, 4);
x_119 = l_Lean_Name_mkStr1(x_118);
x_120 = l_Array_mkArray0(lean_box(0));
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_114);
x_121 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_121, 0, x_114);
lean_ctor_set(x_121, 1, x_119);
lean_ctor_set(x_121, 2, x_120);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_122; 
x_122 = l_Array_empty(lean_box(0));
x_56 = x_89;
x_57 = x_114;
x_58 = x_117;
x_59 = x_120;
x_60 = x_119;
x_61 = x_121;
x_62 = x_88;
x_63 = x_110;
x_64 = x_116;
x_65 = x_122;
goto block_77;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_123 = lean_ctor_get(x_86, 0);
lean_inc(x_123);
lean_dec(x_86);
x_124 = l_Lean_SourceInfo_fromRef(x_123, x_83);
lean_dec(x_123);
x_125 = lean_mk_string_unchecked("only", 4, 4);
x_126 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Array_mkArray1___redArg(x_126);
x_56 = x_89;
x_57 = x_114;
x_58 = x_117;
x_59 = x_120;
x_60 = x_119;
x_61 = x_121;
x_62 = x_88;
x_63 = x_110;
x_64 = x_116;
x_65 = x_127;
goto block_77;
}
}
}
block_141:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_unsigned_to_nat(4u);
x_135 = l_Lean_Syntax_getArg(x_18, x_134);
lean_dec(x_18);
x_136 = l_Lean_Syntax_getOptional_x3f(x_135);
lean_dec(x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; 
x_137 = lean_box(0);
x_84 = x_131;
x_85 = x_132;
x_86 = x_129;
x_87 = x_133;
x_88 = x_130;
x_89 = x_137;
goto block_128;
}
else
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_136);
if (x_138 == 0)
{
x_84 = x_131;
x_85 = x_132;
x_86 = x_129;
x_87 = x_133;
x_88 = x_130;
x_89 = x_136;
goto block_128;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_136, 0);
lean_inc(x_139);
lean_dec(x_136);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_84 = x_131;
x_85 = x_132;
x_86 = x_129;
x_87 = x_133;
x_88 = x_130;
x_89 = x_140;
goto block_128;
}
}
}
block_160:
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_146 = lean_unsigned_to_nat(3u);
x_147 = l_Lean_Syntax_getArg(x_18, x_146);
x_148 = l_Lean_Syntax_isNone(x_147);
if (x_148 == 0)
{
uint8_t x_149; 
lean_inc(x_147);
x_149 = l_Lean_Syntax_matchesNull(x_147, x_13);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec(x_147);
lean_dec(x_142);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_150 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_145);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_151 = l_Lean_Syntax_getArg(x_147, x_12);
lean_dec(x_147);
x_152 = lean_mk_string_unchecked("simpArgs", 8, 8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_153 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_152);
lean_inc(x_151);
x_154 = l_Lean_Syntax_isOfKind(x_151, x_153);
lean_dec(x_153);
if (x_154 == 0)
{
lean_object* x_155; 
lean_dec(x_151);
lean_dec(x_142);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_155 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_145);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = l_Lean_Syntax_getArg(x_151, x_13);
lean_dec(x_151);
x_157 = l_Lean_Syntax_getArgs(x_156);
lean_dec(x_156);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_129 = x_142;
x_130 = x_158;
x_131 = x_143;
x_132 = x_144;
x_133 = x_145;
goto block_141;
}
}
}
else
{
lean_object* x_159; 
lean_dec(x_147);
x_159 = lean_box(0);
x_129 = x_142;
x_130 = x_159;
x_131 = x_143;
x_132 = x_144;
x_133 = x_145;
goto block_141;
}
}
}
block_38:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = l_Array_append(lean_box(0), x_26, x_33);
lean_dec(x_33);
lean_inc(x_24);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_29);
lean_ctor_set(x_35, 2, x_34);
x_36 = l_Lean_Syntax_node6(x_24, x_32, x_25, x_23, x_30, x_27, x_28, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
block_55:
{
lean_object* x_49; lean_object* x_50; 
lean_inc(x_42);
x_49 = l_Array_append(lean_box(0), x_42, x_48);
lean_dec(x_48);
lean_inc(x_44);
lean_inc(x_40);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_44);
lean_ctor_set(x_50, 2, x_49);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_51; 
x_51 = l_Array_empty(lean_box(0));
x_24 = x_40;
x_25 = x_41;
x_26 = x_42;
x_27 = x_43;
x_28 = x_50;
x_29 = x_44;
x_30 = x_45;
x_31 = x_47;
x_32 = x_46;
x_33 = x_51;
goto block_38;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_39, 0);
lean_inc(x_52);
lean_dec(x_39);
x_53 = l_Array_empty(lean_box(0));
x_54 = lean_array_push(x_53, x_52);
x_24 = x_40;
x_25 = x_41;
x_26 = x_42;
x_27 = x_43;
x_28 = x_50;
x_29 = x_44;
x_30 = x_45;
x_31 = x_47;
x_32 = x_46;
x_33 = x_54;
goto block_38;
}
}
block_77:
{
lean_object* x_66; lean_object* x_67; 
lean_inc(x_59);
x_66 = l_Array_append(lean_box(0), x_59, x_65);
lean_dec(x_65);
lean_inc(x_60);
lean_inc(x_57);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_57);
lean_ctor_set(x_67, 1, x_60);
lean_ctor_set(x_67, 2, x_66);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_68; 
x_68 = l_Array_empty(lean_box(0));
x_39 = x_56;
x_40 = x_57;
x_41 = x_58;
x_42 = x_59;
x_43 = x_67;
x_44 = x_60;
x_45 = x_61;
x_46 = x_64;
x_47 = x_63;
x_48 = x_68;
goto block_55;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_62, 0);
lean_inc(x_69);
lean_dec(x_62);
x_70 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_57);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_57);
lean_ctor_set(x_71, 1, x_70);
lean_inc(x_59);
x_72 = l_Array_append(lean_box(0), x_59, x_69);
lean_dec(x_69);
lean_inc(x_60);
lean_inc(x_57);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_57);
lean_ctor_set(x_73, 1, x_60);
lean_ctor_set(x_73, 2, x_72);
x_74 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_57);
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_57);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Array_mkArray3(lean_box(0), x_71, x_73, x_75);
x_39 = x_56;
x_40 = x_57;
x_41 = x_58;
x_42 = x_59;
x_43 = x_67;
x_44 = x_60;
x_45 = x_61;
x_46 = x_64;
x_47 = x_63;
x_48 = x_76;
goto block_55;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___redArg(x_1, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateTryTacticM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_saveState___redArg(x_3, x_5, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateTryTacticM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_Elab_Tactic_SavedState_restore(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateTryTacticM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateTryTacticM___lam__0___boxed), 10, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateTryTacticM___lam__1___boxed), 11, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateTryTacticM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateTryTacticM___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateTryTacticM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateTryTacticM___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_withNonTerminal___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_box(0);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_inc(x_12);
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unbox(x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_16);
x_17 = lean_apply_10(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_withNonTerminal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_box(0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_13);
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unbox(x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_17);
x_18 = lean_apply_10(x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_withNonTerminal___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Try_withNonTerminal___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_withNonTerminal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_Try_withNonTerminal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_tryTacticElabAttribute_unsafe__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = lean_mk_string_unchecked("builtin_try_tactic", 18, 18);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("try_tactic", 10, 10);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_8);
lean_inc(x_6);
x_9 = l_Lean_Name_mkStr3(x_6, x_7, x_8);
x_10 = lean_mk_string_unchecked("Elab", 4, 4);
x_11 = lean_mk_string_unchecked("Try", 3, 3);
x_12 = lean_mk_string_unchecked("TryTactic", 9, 9);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_10);
lean_inc(x_6);
x_13 = l_Lean_Name_mkStr5(x_6, x_10, x_8, x_11, x_12);
x_14 = lean_mk_string_unchecked("tryTacticElabAttribute", 22, 22);
x_15 = l_Lean_Name_mkStr5(x_6, x_10, x_8, x_11, x_14);
x_16 = l_Lean_Elab_mkElabAttribute(lean_box(0), x_3, x_5, x_9, x_13, x_4, x_15, x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_initFn____x40_Lean_Elab_Tactic_Try___hyg_4386_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_Try_tryTacticElabAttribute_unsafe__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getEvalFns___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Elab_Tactic_Try_tryTacticElabAttribute;
x_9 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_8, x_7, x_1);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Tactic_Try_tryTacticElabAttribute;
x_14 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_13, x_12, x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getEvalFns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getEvalFns___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getEvalFns___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getEvalFns___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getEvalFns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getEvalFns(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_focus___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_apply_1(x_1, x_2);
x_13 = l_Lean_Elab_Tactic_focus(lean_box(0), x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_focus(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_apply_1(x_2, x_3);
x_14 = l_Lean_Elab_Tactic_focus(lean_box(0), x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_observing___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_47; 
x_12 = l_Lean_Elab_Tactic_saveState___redArg(x_4, x_6, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_47 = lean_apply_10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Elab_Tactic_saveState___redArg(x_4, x_6, x_8, x_9, x_10, x_49);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
x_54 = lean_box(1);
x_55 = lean_unbox(x_54);
x_56 = l_Lean_Elab_Tactic_SavedState_restore(x_13, x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_53);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 1);
x_59 = lean_ctor_get(x_56, 0);
lean_dec(x_59);
lean_ctor_set(x_56, 1, x_52);
lean_ctor_set(x_56, 0, x_48);
lean_ctor_set(x_50, 1, x_58);
lean_ctor_set(x_50, 0, x_56);
return x_50;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_48);
lean_ctor_set(x_61, 1, x_52);
lean_ctor_set(x_50, 1, x_60);
lean_ctor_set(x_50, 0, x_61);
return x_50;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_62 = lean_ctor_get(x_50, 0);
x_63 = lean_ctor_get(x_50, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_50);
x_64 = lean_box(1);
x_65 = lean_unbox(x_64);
x_66 = l_Lean_Elab_Tactic_SavedState_restore(x_13, x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_63);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_48);
lean_ctor_set(x_69, 1, x_62);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_47);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_47, 0);
x_73 = lean_ctor_get(x_47, 1);
lean_inc(x_73);
lean_inc(x_72);
x_41 = x_47;
x_42 = x_72;
x_43 = x_73;
goto block_46;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_47, 0);
x_75 = lean_ctor_get(x_47, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_47);
lean_inc(x_75);
lean_inc(x_74);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_41 = x_76;
x_42 = x_74;
x_43 = x_75;
goto block_46;
}
}
block_40:
{
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_15);
x_19 = l_Lean_Elab_Tactic_saveState___redArg(x_4, x_6, x_8, x_9, x_10, x_16);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_box(1);
x_24 = lean_unbox(x_23);
x_25 = l_Lean_Elab_Tactic_SavedState_restore(x_13, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_19, 1, x_27);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_19, 1, x_29);
lean_ctor_set(x_19, 0, x_30);
return x_19;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_19);
x_33 = lean_box(1);
x_34 = lean_unbox(x_33);
x_35 = l_Lean_Elab_Tactic_SavedState_restore(x_13, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
 lean_ctor_set_tag(x_38, 1);
}
lean_ctor_set(x_38, 0, x_17);
lean_ctor_set(x_38, 1, x_31);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
block_46:
{
uint8_t x_44; 
x_44 = l_Lean_Exception_isInterrupt(x_42);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = l_Lean_Exception_isRuntime(x_42);
x_15 = x_41;
x_16 = x_43;
x_17 = x_42;
x_18 = x_45;
goto block_40;
}
else
{
x_15 = x_41;
x_16 = x_43;
x_17 = x_42;
x_18 = x_44;
goto block_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_observing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_Try_observing___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = l_Lean_Syntax_structEq(x_1, x_6);
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
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = lean_usize_of_nat(x_3);
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at___Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams_spec__0_spec__0(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
return x_4;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_1, x_3);
lean_inc(x_12);
x_13 = l_Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams_spec__0(x_4, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_array_push(x_4, x_12);
x_5 = x_14;
goto block_10;
}
else
{
lean_dec(x_12);
x_5 = x_4;
goto block_10;
}
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_array_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
x_6 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams_spec__2(x_2, x_3, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams_spec__0_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams_spec__0(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams_spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeSimp_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
lean_inc(x_1);
x_5 = l_Lean_Elab_Tactic_setSimpParams(x_1, x_4);
lean_inc(x_2);
x_6 = l_Lean_Elab_Tactic_setSimpParams(x_2, x_4);
lean_dec(x_4);
x_7 = l_Lean_Syntax_structEq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Elab_Tactic_getSimpParams(x_1);
x_10 = l_Lean_Elab_Tactic_getSimpParams(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams(x_9, x_10);
lean_dec(x_10);
x_12 = l_Lean_Elab_Tactic_setSimpParams(x_1, x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeGrind_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
lean_inc(x_1);
x_5 = l_Lean_Elab_Tactic_setGrindParams(x_1, x_4);
lean_inc(x_2);
x_6 = l_Lean_Elab_Tactic_setGrindParams(x_2, x_4);
lean_dec(x_4);
x_7 = l_Lean_Syntax_structEq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Elab_Tactic_getGrindParams(x_1);
x_10 = l_Lean_Elab_Tactic_getGrindParams(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams(x_9, x_10);
lean_dec(x_10);
x_12 = l_Lean_Elab_Tactic_setGrindParams(x_1, x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_merge_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_1);
x_3 = l_Lean_Syntax_getKind(x_1);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Tactic", 6, 6);
x_7 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = lean_name_eq(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_mk_string_unchecked("grind", 5, 5);
x_11 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
lean_dec(x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeGrind_x3f(x_1, x_2);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeSimp_x3f(x_1, x_2);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_array_fget(x_1, x_4);
lean_inc(x_9);
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_merge_x3f(x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_ctor_get(x_2, 2);
x_19 = lean_nat_add(x_4, x_18);
lean_dec(x_4);
x_3 = x_17;
x_4 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_16);
return x_17;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_mk_string_unchecked("tactic", 6, 6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_box(0);
x_9 = lean_usize_dec_eq(x_4, x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_box(1);
x_19 = l_Lean_instInhabitedTSyntax(x_10);
lean_dec(x_10);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_uget(x_3, x_4);
x_22 = l_Lean_Syntax_getKind(x_21);
x_23 = lean_array_get(x_19, x_1, x_20);
x_24 = l_Lean_Syntax_getKind(x_23);
x_25 = lean_name_eq(x_22, x_24);
lean_dec(x_24);
lean_dec(x_22);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get_uint8(x_26, sizeof(void*)*1 + 6);
x_12 = x_27;
goto block_18;
}
else
{
uint8_t x_28; 
x_28 = l_Array_isEmpty___redArg(x_1);
x_12 = x_28;
goto block_18;
}
block_18:
{
if (x_12 == 0)
{
lean_object* x_13; size_t x_14; size_t x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
x_17 = lean_unbox(x_11);
return x_17;
}
}
}
else
{
lean_object* x_29; uint8_t x_30; 
lean_dec(x_7);
x_29 = lean_box(0);
x_30 = lean_unbox(x_29);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 6);
if (x_16 == 0)
{
goto block_14;
}
else
{
uint8_t x_17; 
x_17 = l_Array_isEmpty___redArg(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_48; uint8_t x_49; 
x_18 = lean_mk_string_unchecked("tactic", 6, 6);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_instInhabitedTSyntax(x_21);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_48 = lean_array_get_size(x_1);
x_49 = lean_nat_dec_lt(x_23, x_48);
if (x_49 == 0)
{
lean_dec(x_48);
goto block_47;
}
else
{
if (x_49 == 0)
{
lean_dec(x_48);
goto block_47;
}
else
{
size_t x_50; size_t x_51; uint8_t x_52; 
x_50 = lean_usize_of_nat(x_23);
x_51 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_52 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f_spec__1(x_1, x_2, x_1, x_50, x_51);
if (x_52 == 0)
{
goto block_47;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_22);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_11);
return x_54;
}
}
}
block_47:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_array_get(x_22, x_1, x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_array_get_size(x_1);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_25);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
x_30 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f_spec__0___redArg(x_1, x_27, x_29, x_25, x_11);
lean_dec(x_27);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_30, 0, x_36);
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_dec(x_30);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_31);
x_41 = !lean_is_exclusive(x_30);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_30, 0);
lean_dec(x_42);
x_43 = lean_ctor_get(x_32, 0);
lean_inc(x_43);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_43);
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_dec(x_30);
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
lean_dec(x_32);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
}
else
{
goto block_14;
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f_spec__1(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
return x_12;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Elab_Tactic_isGrindOnly(x_5);
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
return x_6;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_6 = lean_mk_string_unchecked("tactic", 6, 6);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_instInhabitedTSyntax(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get(x_10, x_2, x_11);
x_13 = lean_mk_string_unchecked("Lean", 4, 4);
x_14 = lean_mk_string_unchecked("Parser", 6, 6);
x_15 = lean_mk_string_unchecked("Tactic", 6, 6);
x_16 = lean_mk_string_unchecked("simp", 4, 4);
x_17 = lean_usize_dec_eq(x_4, x_5);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_26; uint8_t x_27; 
x_18 = lean_box(1);
x_26 = lean_array_uget(x_3, x_4);
x_27 = l_Lean_Elab_Tactic_isGrindOnly(x_26);
if (x_27 == 0)
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_19 = x_1;
goto block_25;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = l_Lean_Syntax_getKind(x_12);
x_29 = l_Lean_Name_mkStr4(x_13, x_14, x_15, x_16);
x_30 = lean_name_eq(x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
x_19 = x_30;
goto block_25;
}
block_25:
{
if (x_19 == 0)
{
lean_object* x_20; size_t x_21; size_t x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_add(x_4, x_21);
x_4 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
x_24 = lean_unbox(x_18);
return x_24;
}
}
}
else
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
return x_32;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__2(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Elab_Tactic_isSimpOnly(x_5);
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
return x_6;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_15; uint8_t x_16; 
x_7 = lean_box(1);
x_15 = lean_array_uget(x_3, x_4);
x_16 = l_Lean_Elab_Tactic_isSimpOnly(x_15);
if (x_16 == 0)
{
x_8 = x_1;
goto block_14;
}
else
{
uint8_t x_17; 
x_17 = l_Array_isEmpty___redArg(x_2);
x_8 = x_17;
goto block_14;
}
block_14:
{
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = lean_unbox(x_7);
return x_13;
}
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
return x_19;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_mk_string_unchecked("tactic", 6, 6);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_instInhabitedTSyntax(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_array_get(x_9, x_1, x_10);
x_13 = l_Lean_Syntax_getKind(x_12);
x_14 = lean_box(1);
x_15 = lean_array_uget(x_2, x_3);
x_16 = l_Lean_Syntax_getKind(x_15);
x_17 = lean_name_eq(x_16, x_13);
lean_dec(x_13);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = lean_unbox(x_14);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = l_Array_isEmpty___redArg(x_1);
if (x_19 == 0)
{
lean_object* x_20; size_t x_21; size_t x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_add(x_3, x_21);
x_3 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
x_24 = lean_unbox(x_14);
return x_24;
}
}
}
else
{
lean_object* x_25; uint8_t x_26; 
lean_dec(x_9);
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
return x_26;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Array_isEmpty___redArg(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_33; lean_object* x_35; uint8_t x_36; 
x_3 = lean_mk_string_unchecked("tactic", 6, 6);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_instInhabitedTSyntax(x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get(x_7, x_1, x_8);
x_10 = l_Lean_Syntax_getKind(x_9);
x_35 = lean_array_get_size(x_1);
x_36 = lean_nat_dec_lt(x_8, x_35);
if (x_36 == 0)
{
lean_dec(x_35);
x_33 = x_2;
goto block_34;
}
else
{
if (x_36 == 0)
{
lean_dec(x_35);
x_33 = x_2;
goto block_34;
}
else
{
size_t x_37; size_t x_38; uint8_t x_39; 
x_37 = lean_usize_of_nat(x_8);
x_38 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_39 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__4(x_1, x_1, x_37, x_38);
x_33 = x_39;
goto block_34;
}
}
block_32:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_15 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_14);
x_16 = lean_name_eq(x_10, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_mk_string_unchecked("grind", 5, 5);
x_18 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_17);
x_19 = lean_name_eq(x_10, x_18);
lean_dec(x_18);
lean_dec(x_10);
if (x_19 == 0)
{
return x_2;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_array_get_size(x_1);
x_21 = lean_nat_dec_lt(x_8, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
return x_2;
}
else
{
if (x_21 == 0)
{
lean_dec(x_20);
return x_2;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = lean_usize_of_nat(x_8);
x_23 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_24 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__0(x_1, x_22, x_23);
if (x_24 == 0)
{
return x_24;
}
else
{
if (x_21 == 0)
{
return x_16;
}
else
{
if (x_21 == 0)
{
return x_16;
}
else
{
uint8_t x_25; 
x_25 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__1(x_24, x_1, x_1, x_22, x_23);
return x_25;
}
}
}
}
}
}
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_26 = lean_array_get_size(x_1);
x_27 = lean_nat_dec_lt(x_8, x_26);
if (x_27 == 0)
{
lean_dec(x_26);
return x_2;
}
else
{
if (x_27 == 0)
{
lean_dec(x_26);
return x_2;
}
else
{
size_t x_28; size_t x_29; uint8_t x_30; 
x_28 = lean_usize_of_nat(x_8);
x_29 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_30 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__2(x_1, x_28, x_29);
if (x_30 == 0)
{
return x_30;
}
else
{
if (x_27 == 0)
{
return x_2;
}
else
{
if (x_27 == 0)
{
return x_2;
}
else
{
uint8_t x_31; 
x_31 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__3(x_30, x_1, x_1, x_28, x_29);
return x_31;
}
}
}
}
}
}
}
block_34:
{
if (x_33 == 0)
{
goto block_32;
}
else
{
if (x_2 == 0)
{
lean_dec(x_10);
return x_2;
}
else
{
goto block_32;
}
}
}
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_box(0);
x_41 = lean_unbox(x_40);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__0(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__1(x_6, x_2, x_3, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__2(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__3(x_6, x_2, x_3, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly_spec__4(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go_spec__0___redArg(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_3, x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_st_ref_get(x_7, x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; lean_object* x_50; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_inc(x_4);
x_17 = lean_array_uset(x_4, x_3, x_16);
x_18 = lean_ctor_get(x_6, 5);
x_19 = l_Lean_SourceInfo_fromRef(x_18, x_1);
x_20 = lean_mk_string_unchecked("Lean", 4, 4);
x_21 = lean_mk_string_unchecked("cdot", 4, 4);
lean_inc(x_20);
x_22 = l_Lean_Name_mkStr2(x_20, x_21);
x_23 = lean_mk_string_unchecked("cdotTk", 6, 6);
lean_inc(x_20);
x_24 = l_Lean_Name_mkStr2(x_20, x_23);
x_25 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_mk_string_unchecked("token", 5, 5);
x_28 = lean_mk_string_unchecked("· ", 3, 2);
x_29 = l_Lean_Name_mkStr2(x_27, x_28);
x_30 = lean_mk_string_unchecked("·", 2, 1);
lean_inc(x_19);
lean_ctor_set_tag(x_12, 2);
lean_ctor_set(x_12, 1, x_30);
lean_ctor_set(x_12, 0, x_19);
lean_inc(x_19);
x_31 = l_Lean_Syntax_node1(x_19, x_29, x_12);
lean_inc(x_19);
x_32 = l_Lean_Syntax_node1(x_19, x_26, x_31);
lean_inc(x_19);
x_33 = l_Lean_Syntax_node1(x_19, x_24, x_32);
x_34 = lean_mk_string_unchecked("Parser", 6, 6);
x_35 = lean_mk_string_unchecked("Tactic", 6, 6);
x_36 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_20);
x_37 = l_Lean_Name_mkStr4(x_20, x_34, x_35, x_36);
x_38 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
x_39 = l_Lean_Name_mkStr4(x_20, x_34, x_35, x_38);
x_40 = lean_mk_string_unchecked("null", 4, 4);
x_41 = l_Lean_Name_mkStr1(x_40);
x_42 = lean_array_uget(x_4, x_3);
lean_dec(x_4);
lean_inc(x_19);
x_43 = l_Lean_Syntax_node1(x_19, x_41, x_42);
lean_inc(x_19);
x_44 = l_Lean_Syntax_node1(x_19, x_39, x_43);
lean_inc(x_19);
x_45 = l_Lean_Syntax_node1(x_19, x_37, x_44);
x_46 = l_Lean_Syntax_node2(x_19, x_22, x_33, x_45);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_usize_of_nat(x_47);
x_49 = lean_usize_add(x_3, x_48);
x_50 = lean_array_uset(x_17, x_3, x_46);
x_3 = x_49;
x_4 = x_50;
x_8 = x_14;
goto _start;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; size_t x_86; size_t x_87; lean_object* x_88; 
x_52 = lean_ctor_get(x_12, 1);
lean_inc(x_52);
lean_dec(x_12);
x_53 = lean_box(0);
lean_inc(x_4);
x_54 = lean_array_uset(x_4, x_3, x_53);
x_55 = lean_ctor_get(x_6, 5);
x_56 = l_Lean_SourceInfo_fromRef(x_55, x_1);
x_57 = lean_mk_string_unchecked("Lean", 4, 4);
x_58 = lean_mk_string_unchecked("cdot", 4, 4);
lean_inc(x_57);
x_59 = l_Lean_Name_mkStr2(x_57, x_58);
x_60 = lean_mk_string_unchecked("cdotTk", 6, 6);
lean_inc(x_57);
x_61 = l_Lean_Name_mkStr2(x_57, x_60);
x_62 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_63 = l_Lean_Name_mkStr1(x_62);
x_64 = lean_mk_string_unchecked("token", 5, 5);
x_65 = lean_mk_string_unchecked("· ", 3, 2);
x_66 = l_Lean_Name_mkStr2(x_64, x_65);
x_67 = lean_mk_string_unchecked("·", 2, 1);
lean_inc(x_56);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_56);
lean_ctor_set(x_68, 1, x_67);
lean_inc(x_56);
x_69 = l_Lean_Syntax_node1(x_56, x_66, x_68);
lean_inc(x_56);
x_70 = l_Lean_Syntax_node1(x_56, x_63, x_69);
lean_inc(x_56);
x_71 = l_Lean_Syntax_node1(x_56, x_61, x_70);
x_72 = lean_mk_string_unchecked("Parser", 6, 6);
x_73 = lean_mk_string_unchecked("Tactic", 6, 6);
x_74 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_57);
x_75 = l_Lean_Name_mkStr4(x_57, x_72, x_73, x_74);
x_76 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
x_77 = l_Lean_Name_mkStr4(x_57, x_72, x_73, x_76);
x_78 = lean_mk_string_unchecked("null", 4, 4);
x_79 = l_Lean_Name_mkStr1(x_78);
x_80 = lean_array_uget(x_4, x_3);
lean_dec(x_4);
lean_inc(x_56);
x_81 = l_Lean_Syntax_node1(x_56, x_79, x_80);
lean_inc(x_56);
x_82 = l_Lean_Syntax_node1(x_56, x_77, x_81);
lean_inc(x_56);
x_83 = l_Lean_Syntax_node1(x_56, x_75, x_82);
x_84 = l_Lean_Syntax_node2(x_56, x_59, x_71, x_83);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_usize_of_nat(x_85);
x_87 = lean_usize_add(x_3, x_86);
x_88 = lean_array_uset(x_54, x_3, x_84);
x_3 = x_87;
x_4 = x_88;
x_8 = x_52;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go_spec__0(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_29; 
x_29 = lean_usize_dec_lt(x_8, x_7);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
lean_dec(x_3);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_9);
lean_ctor_set(x_30, 1, x_10);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_20);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_9);
x_32 = lean_box(0);
x_33 = lean_array_uget(x_6, x_8);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_2, x_34);
lean_inc(x_3);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_3);
lean_inc(x_4);
x_37 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go(x_4, x_5, x_35, x_36, x_1, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_21 = x_32;
x_22 = x_40;
x_23 = x_39;
goto block_28;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_42 = l_Lean_Syntax_getKind(x_33);
x_43 = lean_name_eq(x_42, x_41);
lean_dec(x_42);
if (x_43 == 0)
{
lean_dec(x_33);
x_21 = x_32;
x_22 = x_10;
x_23 = x_20;
goto block_28;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_2, x_44);
lean_inc(x_3);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_33);
lean_ctor_set(x_46, 1, x_3);
lean_inc(x_4);
x_47 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go(x_4, x_5, x_45, x_46, x_1, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_21 = x_32;
x_22 = x_50;
x_23 = x_49;
goto block_28;
}
}
}
block_28:
{
lean_object* x_24; size_t x_25; size_t x_26; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_usize_of_nat(x_24);
x_26 = lean_usize_add(x_8, x_25);
x_8 = x_26;
x_9 = x_21;
x_10 = x_22;
x_20 = x_23;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_7, 1);
x_26 = lean_ctor_get(x_25, 0);
x_27 = lean_array_get_size(x_6);
x_28 = lean_nat_dec_lt(x_26, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_array_get_size(x_2);
x_30 = lean_nat_dec_lt(x_3, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_3);
x_31 = lean_array_mk(x_4);
x_32 = l_Array_reverse(lean_box(0), x_31);
if (lean_obj_tag(x_5) == 0)
{
x_33 = x_30;
goto block_196;
}
else
{
uint8_t x_197; 
x_197 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly(x_32);
if (x_197 == 0)
{
x_33 = x_197;
goto block_196;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_32);
lean_dec(x_1);
x_198 = lean_box(0);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_6);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_16);
return x_200;
}
}
block_196:
{
lean_object* x_34; lean_object* x_35; 
x_34 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f(x_32, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; size_t x_37; lean_object* x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_array_size(x_32);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_usize_of_nat(x_38);
x_40 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go_spec__0___redArg(x_33, x_37, x_39, x_32, x_6, x_14, x_15, x_36);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_41, 0);
x_45 = lean_ctor_get(x_41, 1);
x_46 = lean_st_ref_get(x_15, x_42);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_48 = lean_ctor_get(x_46, 1);
x_49 = lean_ctor_get(x_46, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_14, 5);
x_51 = l_Lean_SourceInfo_fromRef(x_50, x_33);
x_52 = lean_mk_string_unchecked("tactic", 6, 6);
x_53 = l_Lean_Name_mkStr1(x_52);
x_54 = lean_box(0);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 1, x_54);
lean_ctor_set(x_46, 0, x_53);
x_55 = lean_mk_string_unchecked("Lean", 4, 4);
x_56 = lean_mk_string_unchecked("cdot", 4, 4);
lean_inc(x_55);
x_57 = l_Lean_Name_mkStr2(x_55, x_56);
x_58 = lean_mk_string_unchecked("cdotTk", 6, 6);
lean_inc(x_55);
x_59 = l_Lean_Name_mkStr2(x_55, x_58);
x_60 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_61 = l_Lean_Name_mkStr1(x_60);
x_62 = lean_mk_string_unchecked("token", 5, 5);
x_63 = lean_mk_string_unchecked("· ", 3, 2);
x_64 = l_Lean_Name_mkStr2(x_62, x_63);
x_65 = lean_mk_string_unchecked("·", 2, 1);
lean_inc(x_51);
lean_ctor_set_tag(x_41, 2);
lean_ctor_set(x_41, 1, x_65);
lean_ctor_set(x_41, 0, x_51);
lean_inc(x_51);
x_66 = l_Lean_Syntax_node1(x_51, x_64, x_41);
lean_inc(x_51);
x_67 = l_Lean_Syntax_node1(x_51, x_61, x_66);
lean_inc(x_51);
x_68 = l_Lean_Syntax_node1(x_51, x_59, x_67);
x_69 = lean_mk_string_unchecked("Parser", 6, 6);
x_70 = lean_mk_string_unchecked("Tactic", 6, 6);
x_71 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_55);
x_72 = l_Lean_Name_mkStr4(x_55, x_69, x_70, x_71);
x_73 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
x_74 = l_Lean_Name_mkStr4(x_55, x_69, x_70, x_73);
x_75 = lean_mk_string_unchecked("null", 4, 4);
x_76 = l_Lean_Name_mkStr1(x_75);
x_77 = l_Array_mkArray0(lean_box(0));
lean_inc(x_76);
lean_inc(x_51);
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_51);
lean_ctor_set(x_78, 1, x_76);
lean_ctor_set(x_78, 2, x_77);
x_79 = l_Array_mkArray2(lean_box(0), x_1, x_78);
x_80 = lean_mk_string_unchecked("", 0, 0);
x_81 = l_Lean_Syntax_TSepArray_ofElems(x_46, x_80, x_44);
lean_dec(x_44);
lean_dec(x_46);
x_82 = l_Array_append(lean_box(0), x_79, x_81);
lean_dec(x_81);
lean_inc(x_51);
x_83 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_83, 0, x_51);
lean_ctor_set(x_83, 1, x_76);
lean_ctor_set(x_83, 2, x_82);
lean_inc(x_51);
x_84 = l_Lean_Syntax_node1(x_51, x_74, x_83);
lean_inc(x_51);
x_85 = l_Lean_Syntax_node1(x_51, x_72, x_84);
x_86 = l_Lean_Syntax_node2(x_51, x_57, x_68, x_85);
x_17 = x_86;
x_18 = x_45;
x_19 = x_48;
goto block_24;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_87 = lean_ctor_get(x_46, 1);
lean_inc(x_87);
lean_dec(x_46);
x_88 = lean_ctor_get(x_14, 5);
x_89 = l_Lean_SourceInfo_fromRef(x_88, x_33);
x_90 = lean_mk_string_unchecked("tactic", 6, 6);
x_91 = l_Lean_Name_mkStr1(x_90);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_mk_string_unchecked("Lean", 4, 4);
x_95 = lean_mk_string_unchecked("cdot", 4, 4);
lean_inc(x_94);
x_96 = l_Lean_Name_mkStr2(x_94, x_95);
x_97 = lean_mk_string_unchecked("cdotTk", 6, 6);
lean_inc(x_94);
x_98 = l_Lean_Name_mkStr2(x_94, x_97);
x_99 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_100 = l_Lean_Name_mkStr1(x_99);
x_101 = lean_mk_string_unchecked("token", 5, 5);
x_102 = lean_mk_string_unchecked("· ", 3, 2);
x_103 = l_Lean_Name_mkStr2(x_101, x_102);
x_104 = lean_mk_string_unchecked("·", 2, 1);
lean_inc(x_89);
lean_ctor_set_tag(x_41, 2);
lean_ctor_set(x_41, 1, x_104);
lean_ctor_set(x_41, 0, x_89);
lean_inc(x_89);
x_105 = l_Lean_Syntax_node1(x_89, x_103, x_41);
lean_inc(x_89);
x_106 = l_Lean_Syntax_node1(x_89, x_100, x_105);
lean_inc(x_89);
x_107 = l_Lean_Syntax_node1(x_89, x_98, x_106);
x_108 = lean_mk_string_unchecked("Parser", 6, 6);
x_109 = lean_mk_string_unchecked("Tactic", 6, 6);
x_110 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_94);
x_111 = l_Lean_Name_mkStr4(x_94, x_108, x_109, x_110);
x_112 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
x_113 = l_Lean_Name_mkStr4(x_94, x_108, x_109, x_112);
x_114 = lean_mk_string_unchecked("null", 4, 4);
x_115 = l_Lean_Name_mkStr1(x_114);
x_116 = l_Array_mkArray0(lean_box(0));
lean_inc(x_115);
lean_inc(x_89);
x_117 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_117, 0, x_89);
lean_ctor_set(x_117, 1, x_115);
lean_ctor_set(x_117, 2, x_116);
x_118 = l_Array_mkArray2(lean_box(0), x_1, x_117);
x_119 = lean_mk_string_unchecked("", 0, 0);
x_120 = l_Lean_Syntax_TSepArray_ofElems(x_93, x_119, x_44);
lean_dec(x_44);
lean_dec(x_93);
x_121 = l_Array_append(lean_box(0), x_118, x_120);
lean_dec(x_120);
lean_inc(x_89);
x_122 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_122, 0, x_89);
lean_ctor_set(x_122, 1, x_115);
lean_ctor_set(x_122, 2, x_121);
lean_inc(x_89);
x_123 = l_Lean_Syntax_node1(x_89, x_113, x_122);
lean_inc(x_89);
x_124 = l_Lean_Syntax_node1(x_89, x_111, x_123);
x_125 = l_Lean_Syntax_node2(x_89, x_96, x_107, x_124);
x_17 = x_125;
x_18 = x_45;
x_19 = x_87;
goto block_24;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_126 = lean_ctor_get(x_41, 0);
x_127 = lean_ctor_get(x_41, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_41);
x_128 = lean_st_ref_get(x_15, x_42);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_130 = x_128;
} else {
 lean_dec_ref(x_128);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_14, 5);
x_132 = l_Lean_SourceInfo_fromRef(x_131, x_33);
x_133 = lean_mk_string_unchecked("tactic", 6, 6);
x_134 = l_Lean_Name_mkStr1(x_133);
x_135 = lean_box(0);
if (lean_is_scalar(x_130)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_130;
 lean_ctor_set_tag(x_136, 1);
}
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_mk_string_unchecked("Lean", 4, 4);
x_138 = lean_mk_string_unchecked("cdot", 4, 4);
lean_inc(x_137);
x_139 = l_Lean_Name_mkStr2(x_137, x_138);
x_140 = lean_mk_string_unchecked("cdotTk", 6, 6);
lean_inc(x_137);
x_141 = l_Lean_Name_mkStr2(x_137, x_140);
x_142 = lean_mk_string_unchecked("patternIgnore", 13, 13);
x_143 = l_Lean_Name_mkStr1(x_142);
x_144 = lean_mk_string_unchecked("token", 5, 5);
x_145 = lean_mk_string_unchecked("· ", 3, 2);
x_146 = l_Lean_Name_mkStr2(x_144, x_145);
x_147 = lean_mk_string_unchecked("·", 2, 1);
lean_inc(x_132);
x_148 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_148, 0, x_132);
lean_ctor_set(x_148, 1, x_147);
lean_inc(x_132);
x_149 = l_Lean_Syntax_node1(x_132, x_146, x_148);
lean_inc(x_132);
x_150 = l_Lean_Syntax_node1(x_132, x_143, x_149);
lean_inc(x_132);
x_151 = l_Lean_Syntax_node1(x_132, x_141, x_150);
x_152 = lean_mk_string_unchecked("Parser", 6, 6);
x_153 = lean_mk_string_unchecked("Tactic", 6, 6);
x_154 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_137);
x_155 = l_Lean_Name_mkStr4(x_137, x_152, x_153, x_154);
x_156 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
x_157 = l_Lean_Name_mkStr4(x_137, x_152, x_153, x_156);
x_158 = lean_mk_string_unchecked("null", 4, 4);
x_159 = l_Lean_Name_mkStr1(x_158);
x_160 = l_Array_mkArray0(lean_box(0));
lean_inc(x_159);
lean_inc(x_132);
x_161 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_161, 0, x_132);
lean_ctor_set(x_161, 1, x_159);
lean_ctor_set(x_161, 2, x_160);
x_162 = l_Array_mkArray2(lean_box(0), x_1, x_161);
x_163 = lean_mk_string_unchecked("", 0, 0);
x_164 = l_Lean_Syntax_TSepArray_ofElems(x_136, x_163, x_126);
lean_dec(x_126);
lean_dec(x_136);
x_165 = l_Array_append(lean_box(0), x_162, x_164);
lean_dec(x_164);
lean_inc(x_132);
x_166 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_166, 0, x_132);
lean_ctor_set(x_166, 1, x_159);
lean_ctor_set(x_166, 2, x_165);
lean_inc(x_132);
x_167 = l_Lean_Syntax_node1(x_132, x_157, x_166);
lean_inc(x_132);
x_168 = l_Lean_Syntax_node1(x_132, x_155, x_167);
x_169 = l_Lean_Syntax_node2(x_132, x_139, x_151, x_168);
x_17 = x_169;
x_18 = x_127;
x_19 = x_129;
goto block_24;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
lean_dec(x_32);
x_170 = lean_ctor_get(x_34, 1);
lean_inc(x_170);
lean_dec(x_34);
x_171 = lean_ctor_get(x_35, 0);
lean_inc(x_171);
lean_dec(x_35);
x_172 = lean_st_ref_get(x_15, x_170);
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_174 = lean_ctor_get(x_172, 1);
x_175 = lean_ctor_get(x_172, 0);
lean_dec(x_175);
x_176 = lean_ctor_get(x_14, 5);
x_177 = l_Lean_SourceInfo_fromRef(x_176, x_33);
x_178 = lean_mk_string_unchecked("Lean", 4, 4);
x_179 = lean_mk_string_unchecked("Parser", 6, 6);
x_180 = lean_mk_string_unchecked("Tactic", 6, 6);
x_181 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
x_182 = l_Lean_Name_mkStr4(x_178, x_179, x_180, x_181);
x_183 = lean_mk_string_unchecked("<;>", 3, 3);
lean_inc(x_177);
lean_ctor_set_tag(x_172, 2);
lean_ctor_set(x_172, 1, x_183);
lean_ctor_set(x_172, 0, x_177);
x_184 = l_Lean_Syntax_node3(x_177, x_182, x_1, x_172, x_171);
x_17 = x_184;
x_18 = x_6;
x_19 = x_174;
goto block_24;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_185 = lean_ctor_get(x_172, 1);
lean_inc(x_185);
lean_dec(x_172);
x_186 = lean_ctor_get(x_14, 5);
x_187 = l_Lean_SourceInfo_fromRef(x_186, x_33);
x_188 = lean_mk_string_unchecked("Lean", 4, 4);
x_189 = lean_mk_string_unchecked("Parser", 6, 6);
x_190 = lean_mk_string_unchecked("Tactic", 6, 6);
x_191 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
x_192 = l_Lean_Name_mkStr4(x_188, x_189, x_190, x_191);
x_193 = lean_mk_string_unchecked("<;>", 3, 3);
lean_inc(x_187);
x_194 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_194, 0, x_187);
lean_ctor_set(x_194, 1, x_193);
x_195 = l_Lean_Syntax_node3(x_187, x_192, x_1, x_194, x_171);
x_17 = x_195;
x_18 = x_6;
x_19 = x_185;
goto block_24;
}
}
}
}
else
{
lean_object* x_201; uint8_t x_202; 
x_201 = lean_array_fget(x_2, x_3);
x_202 = l_Array_isEmpty___redArg(x_201);
if (x_202 == 0)
{
lean_object* x_203; size_t x_204; lean_object* x_205; size_t x_206; lean_object* x_207; uint8_t x_208; 
x_203 = lean_box(0);
x_204 = lean_array_size(x_201);
x_205 = lean_unsigned_to_nat(0u);
x_206 = lean_usize_of_nat(x_205);
x_207 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go_spec__1(x_5, x_3, x_4, x_1, x_2, x_201, x_204, x_206, x_203, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_201);
lean_dec(x_3);
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; uint8_t x_210; 
x_209 = lean_ctor_get(x_207, 0);
x_210 = !lean_is_exclusive(x_209);
if (x_210 == 0)
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_209, 0);
lean_dec(x_211);
lean_ctor_set(x_209, 0, x_203);
return x_207;
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
lean_dec(x_209);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_203);
lean_ctor_set(x_213, 1, x_212);
lean_ctor_set(x_207, 0, x_213);
return x_207;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_214 = lean_ctor_get(x_207, 0);
x_215 = lean_ctor_get(x_207, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_207);
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
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_203);
lean_ctor_set(x_218, 1, x_216);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_215);
return x_219;
}
}
else
{
lean_object* x_220; uint8_t x_221; 
lean_dec(x_201);
x_220 = lean_st_ref_get(x_15, x_16);
x_221 = !lean_is_exclusive(x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_222 = lean_ctor_get(x_220, 1);
x_223 = lean_ctor_get(x_220, 0);
lean_dec(x_223);
x_224 = lean_ctor_get(x_14, 5);
x_225 = l_Lean_SourceInfo_fromRef(x_224, x_28);
x_226 = lean_mk_string_unchecked("Lean", 4, 4);
x_227 = lean_mk_string_unchecked("Parser", 6, 6);
x_228 = lean_mk_string_unchecked("Tactic", 6, 6);
x_229 = lean_mk_string_unchecked("tacticSorry", 11, 11);
x_230 = l_Lean_Name_mkStr4(x_226, x_227, x_228, x_229);
x_231 = lean_mk_string_unchecked("sorry", 5, 5);
lean_inc(x_225);
lean_ctor_set_tag(x_220, 2);
lean_ctor_set(x_220, 1, x_231);
lean_ctor_set(x_220, 0, x_225);
x_232 = l_Lean_Syntax_node1(x_225, x_230, x_220);
x_233 = lean_unsigned_to_nat(1u);
x_234 = lean_nat_add(x_3, x_233);
lean_dec(x_3);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_4);
x_3 = x_234;
x_4 = x_235;
x_16 = x_222;
goto _start;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_237 = lean_ctor_get(x_220, 1);
lean_inc(x_237);
lean_dec(x_220);
x_238 = lean_ctor_get(x_14, 5);
x_239 = l_Lean_SourceInfo_fromRef(x_238, x_28);
x_240 = lean_mk_string_unchecked("Lean", 4, 4);
x_241 = lean_mk_string_unchecked("Parser", 6, 6);
x_242 = lean_mk_string_unchecked("Tactic", 6, 6);
x_243 = lean_mk_string_unchecked("tacticSorry", 11, 11);
x_244 = l_Lean_Name_mkStr4(x_240, x_241, x_242, x_243);
x_245 = lean_mk_string_unchecked("sorry", 5, 5);
lean_inc(x_239);
x_246 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_246, 0, x_239);
lean_ctor_set(x_246, 1, x_245);
x_247 = l_Lean_Syntax_node1(x_239, x_244, x_246);
x_248 = lean_unsigned_to_nat(1u);
x_249 = lean_nat_add(x_3, x_248);
lean_dec(x_3);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_4);
x_3 = x_249;
x_4 = x_250;
x_16 = x_237;
goto _start;
}
}
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_252 = lean_box(0);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_6);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_16);
return x_254;
}
block_24:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_box(0);
x_21 = lean_array_push(x_18, x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go_spec__0___redArg(x_9, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_18 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_19 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go_spec__0(x_16, x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go_spec__1___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_22 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_23 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_21, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_23;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg(x_1, x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionsCore(x_5);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__2___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_7, x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_6, 5);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_SourceInfo_fromRef(x_15, x_17);
x_19 = lean_mk_string_unchecked("Lean", 4, 4);
x_20 = lean_mk_string_unchecked("Parser", 6, 6);
x_21 = lean_mk_string_unchecked("Tactic", 6, 6);
x_22 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
x_23 = l_Lean_Name_mkStr4(x_19, x_20, x_21, x_22);
x_24 = lean_mk_string_unchecked("<;>", 3, 3);
lean_inc(x_18);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_24);
lean_ctor_set(x_11, 0, x_18);
x_25 = lean_array_uget(x_2, x_4);
lean_inc(x_1);
x_26 = l_Lean_Syntax_node3(x_18, x_23, x_1, x_11, x_25);
x_27 = lean_array_push(x_5, x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_usize_add(x_4, x_29);
x_4 = x_30;
x_5 = x_27;
x_8 = x_13;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; 
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_dec(x_11);
x_33 = lean_ctor_get(x_6, 5);
x_34 = lean_box(0);
x_35 = lean_unbox(x_34);
x_36 = l_Lean_SourceInfo_fromRef(x_33, x_35);
x_37 = lean_mk_string_unchecked("Lean", 4, 4);
x_38 = lean_mk_string_unchecked("Parser", 6, 6);
x_39 = lean_mk_string_unchecked("Tactic", 6, 6);
x_40 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
x_41 = l_Lean_Name_mkStr4(x_37, x_38, x_39, x_40);
x_42 = lean_mk_string_unchecked("<;>", 3, 3);
lean_inc(x_36);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_array_uget(x_2, x_4);
lean_inc(x_1);
x_45 = l_Lean_Syntax_node3(x_36, x_41, x_1, x_43, x_44);
x_46 = lean_array_push(x_5, x_45);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_usize_of_nat(x_47);
x_49 = lean_usize_add(x_4, x_48);
x_4 = x_49;
x_5 = x_46;
x_8 = x_32;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; size_t x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_array_size(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_usize_of_nat(x_13);
lean_inc(x_1);
x_15 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__1(x_12, x_14, x_1);
lean_inc(x_15);
x_16 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll(x_15);
x_17 = lean_usize_dec_eq(x_3, x_4);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs(x_15, x_16);
lean_dec(x_16);
x_19 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll(x_18);
x_20 = lean_array_uget(x_2, x_3);
lean_inc(x_20);
x_21 = l_Lean_Syntax_getKind(x_20);
x_22 = l_Array_contains___at___Lean_HasConstCache_containsUnsafe_spec__0(x_19, x_21);
lean_dec(x_21);
lean_dec(x_19);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_array_push(x_5, x_20);
x_6 = x_23;
goto block_11;
}
else
{
lean_dec(x_20);
x_6 = x_5;
goto block_11;
}
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_1);
return x_5;
}
block_11:
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; lean_object* x_18; size_t x_19; uint8_t x_20; 
x_17 = lean_array_size(x_2);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_dec_lt(x_5, x_4);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
lean_inc(x_2);
x_22 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__1(x_17, x_19, x_2);
lean_inc(x_22);
x_23 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll(x_22);
x_24 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs(x_22, x_23);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = lean_array_uget(x_3, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_inc(x_1);
x_28 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go(x_1, x_24, x_18, x_25, x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_27);
lean_dec(x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_usize_of_nat(x_32);
x_34 = lean_usize_add(x_5, x_33);
x_5 = x_34;
x_6 = x_31;
x_16 = x_30;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__5_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_6);
x_18 = lean_mk_empty_array_with_capacity(x_16);
x_19 = lean_nat_dec_lt(x_16, x_17);
if (x_19 == 0)
{
lean_dec(x_17);
lean_dec(x_6);
x_9 = x_18;
goto block_15;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_17, x_17);
if (x_20 == 0)
{
lean_dec(x_17);
lean_dec(x_6);
x_9 = x_18;
goto block_15;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = lean_usize_of_nat(x_16);
x_22 = lean_usize_of_nat(x_17);
lean_dec(x_17);
lean_inc(x_1);
x_23 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__3(x_1, x_6, x_21, x_22, x_18);
lean_dec(x_6);
x_9 = x_23;
goto block_15;
}
}
block_15:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_6);
x_18 = lean_mk_empty_array_with_capacity(x_16);
x_19 = lean_nat_dec_lt(x_16, x_17);
if (x_19 == 0)
{
lean_dec(x_17);
lean_dec(x_6);
x_9 = x_18;
goto block_15;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_17, x_17);
if (x_20 == 0)
{
lean_dec(x_17);
lean_dec(x_6);
x_9 = x_18;
goto block_15;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = lean_usize_of_nat(x_16);
x_22 = lean_usize_of_nat(x_17);
lean_dec(x_17);
lean_inc(x_1);
x_23 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__3(x_1, x_6, x_21, x_22, x_18);
lean_dec(x_6);
x_9 = x_23;
goto block_15;
}
}
block_15:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_8, x_3, x_9);
x_14 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__5_spec__5(x_1, x_2, x_12, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__7(uint8_t x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_15; uint8_t x_16; 
x_7 = lean_box(1);
x_15 = lean_array_uget(x_3, x_4);
x_16 = l_Array_isEmpty___redArg(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
x_8 = x_1;
goto block_14;
}
else
{
x_8 = x_2;
goto block_14;
}
block_14:
{
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = lean_unbox(x_7);
return x_13;
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__8(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_14; uint8_t x_15; 
x_6 = lean_box(1);
x_14 = lean_array_uget(x_2, x_3);
x_15 = l_Array_isEmpty___redArg(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
x_7 = x_15;
goto block_13;
}
else
{
x_7 = x_1;
goto block_13;
}
block_13:
{
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
uint8_t x_12; 
x_12 = lean_unbox(x_6);
return x_12;
}
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_1, x_2, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__10_spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_22; 
x_22 = lean_usize_dec_lt(x_3, x_2);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_14);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_4);
x_24 = lean_mk_string_unchecked("try", 3, 3);
x_25 = lean_mk_string_unchecked("debug", 5, 5);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
lean_inc(x_26);
x_27 = l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg(x_26, x_12, x_14);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_box(0);
x_32 = lean_unbox(x_29);
lean_dec(x_29);
if (x_32 == 0)
{
lean_free_object(x_27);
lean_dec(x_26);
x_15 = x_31;
x_16 = x_30;
goto block_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_mk_string_unchecked("  ", 2, 2);
x_34 = l_Lean_stringToMessageData(x_33);
lean_dec(x_33);
x_35 = lean_array_uget(x_1, x_3);
x_36 = l_Lean_MessageData_ofSyntax(x_35);
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_36);
lean_ctor_set(x_27, 0, x_34);
x_37 = lean_mk_string_unchecked("", 0, 0);
x_38 = l_Lean_stringToMessageData(x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_26, x_39, x_10, x_11, x_12, x_13, x_30);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_15 = x_31;
x_16 = x_41;
goto block_21;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_27, 0);
x_43 = lean_ctor_get(x_27, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_27);
x_44 = lean_box(0);
x_45 = lean_unbox(x_42);
lean_dec(x_42);
if (x_45 == 0)
{
lean_dec(x_26);
x_15 = x_44;
x_16 = x_43;
goto block_21;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_mk_string_unchecked("  ", 2, 2);
x_47 = l_Lean_stringToMessageData(x_46);
lean_dec(x_46);
x_48 = lean_array_uget(x_1, x_3);
x_49 = l_Lean_MessageData_ofSyntax(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_mk_string_unchecked("", 0, 0);
x_52 = l_Lean_stringToMessageData(x_51);
lean_dec(x_51);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_26, x_53, x_10, x_11, x_12, x_13, x_43);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_15 = x_44;
x_16 = x_55;
goto block_21;
}
}
}
block_21:
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_4 = x_15;
x_14 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_22; 
x_22 = lean_usize_dec_lt(x_3, x_2);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_14);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_4);
x_24 = lean_mk_string_unchecked("try", 3, 3);
x_25 = lean_mk_string_unchecked("debug", 5, 5);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
lean_inc(x_26);
x_27 = l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg(x_26, x_12, x_14);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_box(0);
x_32 = lean_unbox(x_29);
lean_dec(x_29);
if (x_32 == 0)
{
lean_free_object(x_27);
lean_dec(x_26);
x_15 = x_31;
x_16 = x_30;
goto block_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_mk_string_unchecked("  ", 2, 2);
x_34 = l_Lean_stringToMessageData(x_33);
lean_dec(x_33);
x_35 = lean_array_uget(x_1, x_3);
x_36 = l_Lean_MessageData_ofSyntax(x_35);
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_36);
lean_ctor_set(x_27, 0, x_34);
x_37 = lean_mk_string_unchecked("", 0, 0);
x_38 = l_Lean_stringToMessageData(x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_26, x_39, x_10, x_11, x_12, x_13, x_30);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_15 = x_31;
x_16 = x_41;
goto block_21;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_27, 0);
x_43 = lean_ctor_get(x_27, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_27);
x_44 = lean_box(0);
x_45 = lean_unbox(x_42);
lean_dec(x_42);
if (x_45 == 0)
{
lean_dec(x_26);
x_15 = x_44;
x_16 = x_43;
goto block_21;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_mk_string_unchecked("  ", 2, 2);
x_47 = l_Lean_stringToMessageData(x_46);
lean_dec(x_46);
x_48 = lean_array_uget(x_1, x_3);
x_49 = l_Lean_MessageData_ofSyntax(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_mk_string_unchecked("", 0, 0);
x_52 = l_Lean_stringToMessageData(x_51);
lean_dec(x_51);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_26, x_53, x_10, x_11, x_12, x_13, x_43);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_15 = x_44;
x_16 = x_55;
goto block_21;
}
}
}
block_21:
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_3, x_18);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__10_spec__10(x_1, x_2, x_19, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_16);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__12_spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_3, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_mk_string_unchecked("try", 3, 3);
x_18 = lean_mk_string_unchecked("debug", 5, 5);
x_19 = l_Lean_Name_mkStr2(x_17, x_18);
lean_inc(x_19);
x_20 = l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg(x_19, x_12, x_14);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_47; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_array_uget(x_1, x_3);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_4, x_25);
lean_dec(x_4);
x_47 = lean_unbox(x_22);
lean_dec(x_22);
if (x_47 == 0)
{
lean_free_object(x_20);
lean_dec(x_19);
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_12;
x_35 = x_13;
x_36 = x_23;
goto block_46;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_48 = lean_mk_string_unchecked("goal #", 6, 6);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
lean_inc(x_26);
x_50 = l___private_Init_Data_Repr_0__Nat_reprFast(x_26);
x_51 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Lean_MessageData_ofFormat(x_51);
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_52);
lean_ctor_set(x_20, 0, x_49);
x_53 = lean_mk_string_unchecked(" tactics", 8, 8);
x_54 = l_Lean_stringToMessageData(x_53);
lean_dec(x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_20);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_19, x_55, x_10, x_11, x_12, x_13, x_23);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_12;
x_35 = x_13;
x_36 = x_57;
goto block_46;
}
block_46:
{
lean_object* x_37; size_t x_38; lean_object* x_39; size_t x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; 
x_37 = lean_box(0);
x_38 = lean_array_size(x_24);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_usize_of_nat(x_39);
x_41 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__10(x_24, x_38, x_40, x_37, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36);
lean_dec(x_24);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_usize_of_nat(x_25);
x_44 = lean_usize_add(x_3, x_43);
x_3 = x_44;
x_4 = x_26;
x_14 = x_42;
goto _start;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_83; 
x_58 = lean_ctor_get(x_20, 0);
x_59 = lean_ctor_get(x_20, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_20);
x_60 = lean_array_uget(x_1, x_3);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_4, x_61);
lean_dec(x_4);
x_83 = lean_unbox(x_58);
lean_dec(x_58);
if (x_83 == 0)
{
lean_dec(x_19);
x_63 = x_5;
x_64 = x_6;
x_65 = x_7;
x_66 = x_8;
x_67 = x_9;
x_68 = x_10;
x_69 = x_11;
x_70 = x_12;
x_71 = x_13;
x_72 = x_59;
goto block_82;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_84 = lean_mk_string_unchecked("goal #", 6, 6);
x_85 = l_Lean_stringToMessageData(x_84);
lean_dec(x_84);
lean_inc(x_62);
x_86 = l___private_Init_Data_Repr_0__Nat_reprFast(x_62);
x_87 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = l_Lean_MessageData_ofFormat(x_87);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_mk_string_unchecked(" tactics", 8, 8);
x_91 = l_Lean_stringToMessageData(x_90);
lean_dec(x_90);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_19, x_92, x_10, x_11, x_12, x_13, x_59);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_63 = x_5;
x_64 = x_6;
x_65 = x_7;
x_66 = x_8;
x_67 = x_9;
x_68 = x_10;
x_69 = x_11;
x_70 = x_12;
x_71 = x_13;
x_72 = x_94;
goto block_82;
}
block_82:
{
lean_object* x_73; size_t x_74; lean_object* x_75; size_t x_76; lean_object* x_77; lean_object* x_78; size_t x_79; size_t x_80; 
x_73 = lean_box(0);
x_74 = lean_array_size(x_60);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_usize_of_nat(x_75);
x_77 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__10(x_60, x_74, x_76, x_73, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70, x_71, x_72);
lean_dec(x_60);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_usize_of_nat(x_61);
x_80 = lean_usize_add(x_3, x_79);
x_3 = x_80;
x_4 = x_62;
x_14 = x_78;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_3, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_mk_string_unchecked("try", 3, 3);
x_18 = lean_mk_string_unchecked("debug", 5, 5);
x_19 = l_Lean_Name_mkStr2(x_17, x_18);
lean_inc(x_19);
x_20 = l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg(x_19, x_12, x_14);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_47; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_array_uget(x_1, x_3);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_4, x_25);
lean_dec(x_4);
x_47 = lean_unbox(x_22);
lean_dec(x_22);
if (x_47 == 0)
{
lean_free_object(x_20);
lean_dec(x_19);
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_12;
x_35 = x_13;
x_36 = x_23;
goto block_46;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_48 = lean_mk_string_unchecked("goal #", 6, 6);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
lean_inc(x_26);
x_50 = l___private_Init_Data_Repr_0__Nat_reprFast(x_26);
x_51 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Lean_MessageData_ofFormat(x_51);
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_52);
lean_ctor_set(x_20, 0, x_49);
x_53 = lean_mk_string_unchecked(" tactics", 8, 8);
x_54 = l_Lean_stringToMessageData(x_53);
lean_dec(x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_20);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_19, x_55, x_10, x_11, x_12, x_13, x_23);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_12;
x_35 = x_13;
x_36 = x_57;
goto block_46;
}
block_46:
{
lean_object* x_37; size_t x_38; lean_object* x_39; size_t x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; 
x_37 = lean_box(0);
x_38 = lean_array_size(x_24);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_usize_of_nat(x_39);
x_41 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__10(x_24, x_38, x_40, x_37, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36);
lean_dec(x_24);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_usize_of_nat(x_25);
x_44 = lean_usize_add(x_3, x_43);
x_45 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__12_spec__12(x_1, x_2, x_44, x_26, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_42);
return x_45;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_83; 
x_58 = lean_ctor_get(x_20, 0);
x_59 = lean_ctor_get(x_20, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_20);
x_60 = lean_array_uget(x_1, x_3);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_4, x_61);
lean_dec(x_4);
x_83 = lean_unbox(x_58);
lean_dec(x_58);
if (x_83 == 0)
{
lean_dec(x_19);
x_63 = x_5;
x_64 = x_6;
x_65 = x_7;
x_66 = x_8;
x_67 = x_9;
x_68 = x_10;
x_69 = x_11;
x_70 = x_12;
x_71 = x_13;
x_72 = x_59;
goto block_82;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_84 = lean_mk_string_unchecked("goal #", 6, 6);
x_85 = l_Lean_stringToMessageData(x_84);
lean_dec(x_84);
lean_inc(x_62);
x_86 = l___private_Init_Data_Repr_0__Nat_reprFast(x_62);
x_87 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = l_Lean_MessageData_ofFormat(x_87);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_mk_string_unchecked(" tactics", 8, 8);
x_91 = l_Lean_stringToMessageData(x_90);
lean_dec(x_90);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_19, x_92, x_10, x_11, x_12, x_13, x_59);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_63 = x_5;
x_64 = x_6;
x_65 = x_7;
x_66 = x_8;
x_67 = x_9;
x_68 = x_10;
x_69 = x_11;
x_70 = x_12;
x_71 = x_13;
x_72 = x_94;
goto block_82;
}
block_82:
{
lean_object* x_73; size_t x_74; lean_object* x_75; size_t x_76; lean_object* x_77; lean_object* x_78; size_t x_79; size_t x_80; lean_object* x_81; 
x_73 = lean_box(0);
x_74 = lean_array_size(x_60);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_usize_of_nat(x_75);
x_77 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__10(x_60, x_74, x_76, x_73, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70, x_71, x_72);
lean_dec(x_60);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_usize_of_nat(x_61);
x_80 = lean_usize_add(x_3, x_79);
x_81 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__12_spec__12(x_1, x_2, x_80, x_62, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_78);
return x_81;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_mk_empty_array_with_capacity(x_1);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll(x_2);
x_21 = lean_array_size(x_20);
lean_inc(x_3);
x_22 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__2___redArg(x_3, x_20, x_21, x_4, x_19, x_16, x_17, x_18);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_mk_string_unchecked("chain", 5, 5);
x_27 = l_Lean_Name_mkStr3(x_5, x_6, x_26);
lean_inc(x_27);
x_28 = l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg(x_27, x_16, x_25);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_115; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_box(0);
x_88 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs(x_2, x_20);
lean_dec(x_20);
x_115 = lean_unbox(x_30);
lean_dec(x_30);
if (x_115 == 0)
{
lean_free_object(x_28);
lean_dec(x_27);
lean_free_object(x_22);
x_89 = x_24;
x_90 = x_9;
x_91 = x_10;
x_92 = x_11;
x_93 = x_12;
x_94 = x_13;
x_95 = x_14;
x_96 = x_15;
x_97 = x_16;
x_98 = x_17;
x_99 = x_31;
goto block_114;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_116 = lean_mk_string_unchecked("kinds: ", 7, 7);
x_117 = l_Lean_stringToMessageData(x_116);
lean_dec(x_116);
lean_inc(x_88);
x_118 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll(x_88);
x_119 = lean_array_to_list(x_118);
x_120 = lean_box(0);
x_121 = l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(x_119, x_120);
x_122 = l_Lean_MessageData_ofList(x_121);
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_122);
lean_ctor_set(x_28, 0, x_117);
x_123 = lean_mk_string_unchecked("", 0, 0);
x_124 = l_Lean_stringToMessageData(x_123);
lean_dec(x_123);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_124);
lean_ctor_set(x_22, 0, x_28);
x_125 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_27, x_22, x_14, x_15, x_16, x_17, x_31);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_89 = x_24;
x_90 = x_9;
x_91 = x_10;
x_92 = x_11;
x_93 = x_12;
x_94 = x_13;
x_95 = x_14;
x_96 = x_15;
x_97 = x_16;
x_98 = x_17;
x_99 = x_126;
goto block_114;
}
block_51:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_box(0);
x_46 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go(x_3, x_44, x_1, x_32, x_45, x_34, x_39, x_38, x_41, x_37, x_36, x_33, x_43, x_42, x_40, x_35);
lean_dec(x_44);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg(x_49, x_33, x_43, x_42, x_40, x_48);
lean_dec(x_49);
return x_50;
}
block_66:
{
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_62);
lean_dec(x_3);
lean_dec(x_1);
x_65 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg(x_53, x_52, x_63, x_61, x_60, x_55);
lean_dec(x_53);
return x_65;
}
else
{
x_33 = x_52;
x_34 = x_53;
x_35 = x_55;
x_36 = x_54;
x_37 = x_58;
x_38 = x_57;
x_39 = x_56;
x_40 = x_60;
x_41 = x_59;
x_42 = x_61;
x_43 = x_63;
x_44 = x_62;
goto block_51;
}
}
block_87:
{
uint8_t x_80; 
x_80 = l_Array_isEmpty___redArg(x_68);
if (x_80 == 0)
{
x_52 = x_67;
x_53 = x_68;
x_54 = x_70;
x_55 = x_69;
x_56 = x_73;
x_57 = x_72;
x_58 = x_71;
x_59 = x_75;
x_60 = x_74;
x_61 = x_76;
x_62 = x_78;
x_63 = x_77;
x_64 = x_80;
goto block_66;
}
else
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_array_get_size(x_78);
x_82 = lean_nat_dec_lt(x_1, x_81);
if (x_82 == 0)
{
lean_object* x_83; 
lean_dec(x_81);
lean_dec(x_78);
lean_dec(x_3);
lean_dec(x_1);
x_83 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg(x_68, x_67, x_77, x_76, x_74, x_69);
lean_dec(x_68);
return x_83;
}
else
{
if (x_82 == 0)
{
lean_object* x_84; 
lean_dec(x_81);
lean_dec(x_78);
lean_dec(x_3);
lean_dec(x_1);
x_84 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg(x_68, x_67, x_77, x_76, x_74, x_69);
lean_dec(x_68);
return x_84;
}
else
{
size_t x_85; uint8_t x_86; 
x_85 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_86 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__7(x_80, x_79, x_78, x_4, x_85);
x_52 = x_67;
x_53 = x_68;
x_54 = x_70;
x_55 = x_69;
x_56 = x_73;
x_57 = x_72;
x_58 = x_71;
x_59 = x_75;
x_60 = x_74;
x_61 = x_76;
x_62 = x_78;
x_63 = x_77;
x_64 = x_86;
goto block_66;
}
}
}
}
block_114:
{
lean_object* x_100; size_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; size_t x_105; lean_object* x_106; uint8_t x_107; 
lean_inc(x_88);
x_100 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll(x_88);
x_101 = lean_array_size(x_100);
lean_inc(x_7);
lean_inc(x_3);
x_102 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__4(x_3, x_7, x_100, x_101, x_4, x_89, x_90, x_91, x_92, x_93, x_94, x_95, x_96, x_97, x_98, x_99);
lean_dec(x_100);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_array_size(x_88);
x_106 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__5(x_7, x_105, x_4, x_88);
x_107 = l_Array_isEmpty___redArg(x_103);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_array_get_size(x_106);
x_109 = lean_nat_dec_lt(x_1, x_108);
if (x_109 == 0)
{
lean_dec(x_108);
x_33 = x_95;
x_34 = x_103;
x_35 = x_104;
x_36 = x_94;
x_37 = x_93;
x_38 = x_91;
x_39 = x_90;
x_40 = x_98;
x_41 = x_92;
x_42 = x_97;
x_43 = x_96;
x_44 = x_106;
goto block_51;
}
else
{
if (x_109 == 0)
{
lean_dec(x_108);
x_33 = x_95;
x_34 = x_103;
x_35 = x_104;
x_36 = x_94;
x_37 = x_93;
x_38 = x_91;
x_39 = x_90;
x_40 = x_98;
x_41 = x_92;
x_42 = x_97;
x_43 = x_96;
x_44 = x_106;
goto block_51;
}
else
{
size_t x_110; uint8_t x_111; 
x_110 = lean_usize_of_nat(x_108);
lean_dec(x_108);
x_111 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__8(x_109, x_106, x_4, x_110);
if (x_111 == 0)
{
x_33 = x_95;
x_34 = x_103;
x_35 = x_104;
x_36 = x_94;
x_37 = x_93;
x_38 = x_91;
x_39 = x_90;
x_40 = x_98;
x_41 = x_92;
x_42 = x_97;
x_43 = x_96;
x_44 = x_106;
goto block_51;
}
else
{
x_67 = x_95;
x_68 = x_103;
x_69 = x_104;
x_70 = x_94;
x_71 = x_93;
x_72 = x_91;
x_73 = x_90;
x_74 = x_98;
x_75 = x_92;
x_76 = x_97;
x_77 = x_96;
x_78 = x_106;
x_79 = x_107;
goto block_87;
}
}
}
}
else
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_box(0);
x_113 = lean_unbox(x_112);
x_67 = x_95;
x_68 = x_103;
x_69 = x_104;
x_70 = x_94;
x_71 = x_93;
x_72 = x_91;
x_73 = x_90;
x_74 = x_98;
x_75 = x_92;
x_76 = x_97;
x_77 = x_96;
x_78 = x_106;
x_79 = x_113;
goto block_87;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_212; 
x_127 = lean_ctor_get(x_28, 0);
x_128 = lean_ctor_get(x_28, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_28);
x_129 = lean_box(0);
x_185 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs(x_2, x_20);
lean_dec(x_20);
x_212 = lean_unbox(x_127);
lean_dec(x_127);
if (x_212 == 0)
{
lean_dec(x_27);
lean_free_object(x_22);
x_186 = x_24;
x_187 = x_9;
x_188 = x_10;
x_189 = x_11;
x_190 = x_12;
x_191 = x_13;
x_192 = x_14;
x_193 = x_15;
x_194 = x_16;
x_195 = x_17;
x_196 = x_128;
goto block_211;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_213 = lean_mk_string_unchecked("kinds: ", 7, 7);
x_214 = l_Lean_stringToMessageData(x_213);
lean_dec(x_213);
lean_inc(x_185);
x_215 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll(x_185);
x_216 = lean_array_to_list(x_215);
x_217 = lean_box(0);
x_218 = l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(x_216, x_217);
x_219 = l_Lean_MessageData_ofList(x_218);
x_220 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_220, 0, x_214);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_mk_string_unchecked("", 0, 0);
x_222 = l_Lean_stringToMessageData(x_221);
lean_dec(x_221);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_222);
lean_ctor_set(x_22, 0, x_220);
x_223 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_27, x_22, x_14, x_15, x_16, x_17, x_128);
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
lean_dec(x_223);
x_186 = x_24;
x_187 = x_9;
x_188 = x_10;
x_189 = x_11;
x_190 = x_12;
x_191 = x_13;
x_192 = x_14;
x_193 = x_15;
x_194 = x_16;
x_195 = x_17;
x_196 = x_224;
goto block_211;
}
block_148:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = lean_box(0);
x_143 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go(x_3, x_141, x_1, x_129, x_142, x_131, x_136, x_135, x_138, x_134, x_133, x_130, x_140, x_139, x_137, x_132);
lean_dec(x_141);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg(x_146, x_130, x_140, x_139, x_137, x_145);
lean_dec(x_146);
return x_147;
}
block_163:
{
if (x_161 == 0)
{
lean_object* x_162; 
lean_dec(x_159);
lean_dec(x_3);
lean_dec(x_1);
x_162 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg(x_150, x_149, x_160, x_158, x_157, x_152);
lean_dec(x_150);
return x_162;
}
else
{
x_130 = x_149;
x_131 = x_150;
x_132 = x_152;
x_133 = x_151;
x_134 = x_155;
x_135 = x_154;
x_136 = x_153;
x_137 = x_157;
x_138 = x_156;
x_139 = x_158;
x_140 = x_160;
x_141 = x_159;
goto block_148;
}
}
block_184:
{
uint8_t x_177; 
x_177 = l_Array_isEmpty___redArg(x_165);
if (x_177 == 0)
{
x_149 = x_164;
x_150 = x_165;
x_151 = x_167;
x_152 = x_166;
x_153 = x_170;
x_154 = x_169;
x_155 = x_168;
x_156 = x_172;
x_157 = x_171;
x_158 = x_173;
x_159 = x_175;
x_160 = x_174;
x_161 = x_177;
goto block_163;
}
else
{
lean_object* x_178; uint8_t x_179; 
x_178 = lean_array_get_size(x_175);
x_179 = lean_nat_dec_lt(x_1, x_178);
if (x_179 == 0)
{
lean_object* x_180; 
lean_dec(x_178);
lean_dec(x_175);
lean_dec(x_3);
lean_dec(x_1);
x_180 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg(x_165, x_164, x_174, x_173, x_171, x_166);
lean_dec(x_165);
return x_180;
}
else
{
if (x_179 == 0)
{
lean_object* x_181; 
lean_dec(x_178);
lean_dec(x_175);
lean_dec(x_3);
lean_dec(x_1);
x_181 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg(x_165, x_164, x_174, x_173, x_171, x_166);
lean_dec(x_165);
return x_181;
}
else
{
size_t x_182; uint8_t x_183; 
x_182 = lean_usize_of_nat(x_178);
lean_dec(x_178);
x_183 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__7(x_177, x_176, x_175, x_4, x_182);
x_149 = x_164;
x_150 = x_165;
x_151 = x_167;
x_152 = x_166;
x_153 = x_170;
x_154 = x_169;
x_155 = x_168;
x_156 = x_172;
x_157 = x_171;
x_158 = x_173;
x_159 = x_175;
x_160 = x_174;
x_161 = x_183;
goto block_163;
}
}
}
}
block_211:
{
lean_object* x_197; size_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; size_t x_202; lean_object* x_203; uint8_t x_204; 
lean_inc(x_185);
x_197 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll(x_185);
x_198 = lean_array_size(x_197);
lean_inc(x_7);
lean_inc(x_3);
x_199 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__4(x_3, x_7, x_197, x_198, x_4, x_186, x_187, x_188, x_189, x_190, x_191, x_192, x_193, x_194, x_195, x_196);
lean_dec(x_197);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = lean_array_size(x_185);
x_203 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__5(x_7, x_202, x_4, x_185);
x_204 = l_Array_isEmpty___redArg(x_200);
if (x_204 == 0)
{
lean_object* x_205; uint8_t x_206; 
x_205 = lean_array_get_size(x_203);
x_206 = lean_nat_dec_lt(x_1, x_205);
if (x_206 == 0)
{
lean_dec(x_205);
x_130 = x_192;
x_131 = x_200;
x_132 = x_201;
x_133 = x_191;
x_134 = x_190;
x_135 = x_188;
x_136 = x_187;
x_137 = x_195;
x_138 = x_189;
x_139 = x_194;
x_140 = x_193;
x_141 = x_203;
goto block_148;
}
else
{
if (x_206 == 0)
{
lean_dec(x_205);
x_130 = x_192;
x_131 = x_200;
x_132 = x_201;
x_133 = x_191;
x_134 = x_190;
x_135 = x_188;
x_136 = x_187;
x_137 = x_195;
x_138 = x_189;
x_139 = x_194;
x_140 = x_193;
x_141 = x_203;
goto block_148;
}
else
{
size_t x_207; uint8_t x_208; 
x_207 = lean_usize_of_nat(x_205);
lean_dec(x_205);
x_208 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__8(x_206, x_203, x_4, x_207);
if (x_208 == 0)
{
x_130 = x_192;
x_131 = x_200;
x_132 = x_201;
x_133 = x_191;
x_134 = x_190;
x_135 = x_188;
x_136 = x_187;
x_137 = x_195;
x_138 = x_189;
x_139 = x_194;
x_140 = x_193;
x_141 = x_203;
goto block_148;
}
else
{
x_164 = x_192;
x_165 = x_200;
x_166 = x_201;
x_167 = x_191;
x_168 = x_190;
x_169 = x_188;
x_170 = x_187;
x_171 = x_195;
x_172 = x_189;
x_173 = x_194;
x_174 = x_193;
x_175 = x_203;
x_176 = x_204;
goto block_184;
}
}
}
}
else
{
lean_object* x_209; uint8_t x_210; 
x_209 = lean_box(0);
x_210 = lean_unbox(x_209);
x_164 = x_192;
x_165 = x_200;
x_166 = x_201;
x_167 = x_191;
x_168 = x_190;
x_169 = x_188;
x_170 = x_187;
x_171 = x_195;
x_172 = x_189;
x_173 = x_194;
x_174 = x_193;
x_175 = x_203;
x_176 = x_210;
goto block_184;
}
}
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_316; 
x_225 = lean_ctor_get(x_22, 0);
x_226 = lean_ctor_get(x_22, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_22);
x_227 = lean_mk_string_unchecked("chain", 5, 5);
x_228 = l_Lean_Name_mkStr3(x_5, x_6, x_227);
lean_inc(x_228);
x_229 = l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg(x_228, x_16, x_226);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_232 = x_229;
} else {
 lean_dec_ref(x_229);
 x_232 = lean_box(0);
}
x_233 = lean_box(0);
x_289 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs(x_2, x_20);
lean_dec(x_20);
x_316 = lean_unbox(x_230);
lean_dec(x_230);
if (x_316 == 0)
{
lean_dec(x_232);
lean_dec(x_228);
x_290 = x_225;
x_291 = x_9;
x_292 = x_10;
x_293 = x_11;
x_294 = x_12;
x_295 = x_13;
x_296 = x_14;
x_297 = x_15;
x_298 = x_16;
x_299 = x_17;
x_300 = x_231;
goto block_315;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_317 = lean_mk_string_unchecked("kinds: ", 7, 7);
x_318 = l_Lean_stringToMessageData(x_317);
lean_dec(x_317);
lean_inc(x_289);
x_319 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll(x_289);
x_320 = lean_array_to_list(x_319);
x_321 = lean_box(0);
x_322 = l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(x_320, x_321);
x_323 = l_Lean_MessageData_ofList(x_322);
if (lean_is_scalar(x_232)) {
 x_324 = lean_alloc_ctor(7, 2, 0);
} else {
 x_324 = x_232;
 lean_ctor_set_tag(x_324, 7);
}
lean_ctor_set(x_324, 0, x_318);
lean_ctor_set(x_324, 1, x_323);
x_325 = lean_mk_string_unchecked("", 0, 0);
x_326 = l_Lean_stringToMessageData(x_325);
lean_dec(x_325);
x_327 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_327, 0, x_324);
lean_ctor_set(x_327, 1, x_326);
x_328 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_228, x_327, x_14, x_15, x_16, x_17, x_231);
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
lean_dec(x_328);
x_290 = x_225;
x_291 = x_9;
x_292 = x_10;
x_293 = x_11;
x_294 = x_12;
x_295 = x_13;
x_296 = x_14;
x_297 = x_15;
x_298 = x_16;
x_299 = x_17;
x_300 = x_329;
goto block_315;
}
block_252:
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_246 = lean_box(0);
x_247 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go(x_3, x_245, x_1, x_233, x_246, x_235, x_240, x_239, x_242, x_238, x_237, x_234, x_244, x_243, x_241, x_236);
lean_dec(x_245);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg(x_250, x_234, x_244, x_243, x_241, x_249);
lean_dec(x_250);
return x_251;
}
block_267:
{
if (x_265 == 0)
{
lean_object* x_266; 
lean_dec(x_263);
lean_dec(x_3);
lean_dec(x_1);
x_266 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg(x_254, x_253, x_264, x_262, x_261, x_256);
lean_dec(x_254);
return x_266;
}
else
{
x_234 = x_253;
x_235 = x_254;
x_236 = x_256;
x_237 = x_255;
x_238 = x_259;
x_239 = x_258;
x_240 = x_257;
x_241 = x_261;
x_242 = x_260;
x_243 = x_262;
x_244 = x_264;
x_245 = x_263;
goto block_252;
}
}
block_288:
{
uint8_t x_281; 
x_281 = l_Array_isEmpty___redArg(x_269);
if (x_281 == 0)
{
x_253 = x_268;
x_254 = x_269;
x_255 = x_271;
x_256 = x_270;
x_257 = x_274;
x_258 = x_273;
x_259 = x_272;
x_260 = x_276;
x_261 = x_275;
x_262 = x_277;
x_263 = x_279;
x_264 = x_278;
x_265 = x_281;
goto block_267;
}
else
{
lean_object* x_282; uint8_t x_283; 
x_282 = lean_array_get_size(x_279);
x_283 = lean_nat_dec_lt(x_1, x_282);
if (x_283 == 0)
{
lean_object* x_284; 
lean_dec(x_282);
lean_dec(x_279);
lean_dec(x_3);
lean_dec(x_1);
x_284 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg(x_269, x_268, x_278, x_277, x_275, x_270);
lean_dec(x_269);
return x_284;
}
else
{
if (x_283 == 0)
{
lean_object* x_285; 
lean_dec(x_282);
lean_dec(x_279);
lean_dec(x_3);
lean_dec(x_1);
x_285 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg(x_269, x_268, x_278, x_277, x_275, x_270);
lean_dec(x_269);
return x_285;
}
else
{
size_t x_286; uint8_t x_287; 
x_286 = lean_usize_of_nat(x_282);
lean_dec(x_282);
x_287 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__7(x_281, x_280, x_279, x_4, x_286);
x_253 = x_268;
x_254 = x_269;
x_255 = x_271;
x_256 = x_270;
x_257 = x_274;
x_258 = x_273;
x_259 = x_272;
x_260 = x_276;
x_261 = x_275;
x_262 = x_277;
x_263 = x_279;
x_264 = x_278;
x_265 = x_287;
goto block_267;
}
}
}
}
block_315:
{
lean_object* x_301; size_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; size_t x_306; lean_object* x_307; uint8_t x_308; 
lean_inc(x_289);
x_301 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll(x_289);
x_302 = lean_array_size(x_301);
lean_inc(x_7);
lean_inc(x_3);
x_303 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__4(x_3, x_7, x_301, x_302, x_4, x_290, x_291, x_292, x_293, x_294, x_295, x_296, x_297, x_298, x_299, x_300);
lean_dec(x_301);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
x_306 = lean_array_size(x_289);
x_307 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__5(x_7, x_306, x_4, x_289);
x_308 = l_Array_isEmpty___redArg(x_304);
if (x_308 == 0)
{
lean_object* x_309; uint8_t x_310; 
x_309 = lean_array_get_size(x_307);
x_310 = lean_nat_dec_lt(x_1, x_309);
if (x_310 == 0)
{
lean_dec(x_309);
x_234 = x_296;
x_235 = x_304;
x_236 = x_305;
x_237 = x_295;
x_238 = x_294;
x_239 = x_292;
x_240 = x_291;
x_241 = x_299;
x_242 = x_293;
x_243 = x_298;
x_244 = x_297;
x_245 = x_307;
goto block_252;
}
else
{
if (x_310 == 0)
{
lean_dec(x_309);
x_234 = x_296;
x_235 = x_304;
x_236 = x_305;
x_237 = x_295;
x_238 = x_294;
x_239 = x_292;
x_240 = x_291;
x_241 = x_299;
x_242 = x_293;
x_243 = x_298;
x_244 = x_297;
x_245 = x_307;
goto block_252;
}
else
{
size_t x_311; uint8_t x_312; 
x_311 = lean_usize_of_nat(x_309);
lean_dec(x_309);
x_312 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__8(x_310, x_307, x_4, x_311);
if (x_312 == 0)
{
x_234 = x_296;
x_235 = x_304;
x_236 = x_305;
x_237 = x_295;
x_238 = x_294;
x_239 = x_292;
x_240 = x_291;
x_241 = x_299;
x_242 = x_293;
x_243 = x_298;
x_244 = x_297;
x_245 = x_307;
goto block_252;
}
else
{
x_268 = x_296;
x_269 = x_304;
x_270 = x_305;
x_271 = x_295;
x_272 = x_294;
x_273 = x_292;
x_274 = x_291;
x_275 = x_299;
x_276 = x_293;
x_277 = x_298;
x_278 = x_297;
x_279 = x_307;
x_280 = x_308;
goto block_288;
}
}
}
}
else
{
lean_object* x_313; uint8_t x_314; 
x_313 = lean_box(0);
x_314 = lean_unbox(x_313);
x_268 = x_296;
x_269 = x_304;
x_270 = x_305;
x_271 = x_295;
x_272 = x_294;
x_273 = x_292;
x_274 = x_291;
x_275 = x_299;
x_276 = x_293;
x_277 = x_298;
x_278 = x_297;
x_279 = x_307;
x_280 = x_314;
goto block_288;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_mk_string_unchecked("try", 3, 3);
x_14 = lean_mk_string_unchecked("debug", 5, 5);
lean_inc(x_14);
lean_inc(x_13);
x_15 = l_Lean_Name_mkStr2(x_13, x_14);
lean_inc(x_15);
x_16 = l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg(x_15, x_10, x_12);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_51; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_array_size(x_2);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_usize_of_nat(x_21);
lean_inc(x_2);
x_23 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__1(x_20, x_22, x_2);
x_51 = lean_unbox(x_18);
lean_dec(x_18);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_free_object(x_16);
lean_dec(x_15);
x_52 = lean_box(0);
x_53 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lam__0(x_21, x_23, x_1, x_22, x_13, x_14, x_2, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_inc(x_15);
x_54 = l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg(x_15, x_10, x_19);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_free_object(x_16);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_24 = x_3;
x_25 = x_4;
x_26 = x_5;
x_27 = x_6;
x_28 = x_7;
x_29 = x_8;
x_30 = x_9;
x_31 = x_10;
x_32 = x_11;
x_33 = x_57;
goto block_50;
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_54);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_54, 1);
x_60 = lean_ctor_get(x_54, 0);
lean_dec(x_60);
x_61 = lean_mk_string_unchecked("mkChainResultCore tac1", 22, 22);
x_62 = l_Lean_stringToMessageData(x_61);
lean_dec(x_61);
lean_inc(x_1);
x_63 = l_Lean_MessageData_ofSyntax(x_1);
x_64 = l_Lean_indentD(x_63);
lean_ctor_set_tag(x_54, 7);
lean_ctor_set(x_54, 1, x_64);
lean_ctor_set(x_54, 0, x_62);
x_65 = lean_mk_string_unchecked("", 0, 0);
x_66 = l_Lean_stringToMessageData(x_65);
lean_dec(x_65);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_66);
lean_ctor_set(x_16, 0, x_54);
lean_inc(x_15);
x_67 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_15, x_16, x_8, x_9, x_10, x_11, x_59);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_24 = x_3;
x_25 = x_4;
x_26 = x_5;
x_27 = x_6;
x_28 = x_7;
x_29 = x_8;
x_30 = x_9;
x_31 = x_10;
x_32 = x_11;
x_33 = x_68;
goto block_50;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_69 = lean_ctor_get(x_54, 1);
lean_inc(x_69);
lean_dec(x_54);
x_70 = lean_mk_string_unchecked("mkChainResultCore tac1", 22, 22);
x_71 = l_Lean_stringToMessageData(x_70);
lean_dec(x_70);
lean_inc(x_1);
x_72 = l_Lean_MessageData_ofSyntax(x_1);
x_73 = l_Lean_indentD(x_72);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_mk_string_unchecked("", 0, 0);
x_76 = l_Lean_stringToMessageData(x_75);
lean_dec(x_75);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_76);
lean_ctor_set(x_16, 0, x_74);
lean_inc(x_15);
x_77 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_15, x_16, x_8, x_9, x_10, x_11, x_69);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_24 = x_3;
x_25 = x_4;
x_26 = x_5;
x_27 = x_6;
x_28 = x_7;
x_29 = x_8;
x_30 = x_9;
x_31 = x_10;
x_32 = x_11;
x_33 = x_78;
goto block_50;
}
}
}
block_50:
{
size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_array_size(x_23);
x_35 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__12(x_23, x_34, x_22, x_21, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
lean_inc(x_15);
x_37 = l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg(x_15, x_31, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_15);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_box(0);
x_42 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lam__0(x_21, x_23, x_1, x_22, x_13, x_14, x_2, x_41, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_dec(x_37);
x_44 = lean_mk_string_unchecked("mkChainResult -----", 19, 19);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_15, x_45, x_29, x_30, x_31, x_32, x_43);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_box(0);
x_49 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lam__0(x_21, x_23, x_1, x_22, x_13, x_14, x_2, x_48, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_47);
return x_49;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; size_t x_81; lean_object* x_82; size_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_112; 
x_79 = lean_ctor_get(x_16, 0);
x_80 = lean_ctor_get(x_16, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_16);
x_81 = lean_array_size(x_2);
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_usize_of_nat(x_82);
lean_inc(x_2);
x_84 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__1(x_81, x_83, x_2);
x_112 = lean_unbox(x_79);
lean_dec(x_79);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_15);
x_113 = lean_box(0);
x_114 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lam__0(x_82, x_84, x_1, x_83, x_13, x_14, x_2, x_113, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_80);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_inc(x_15);
x_115 = l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg(x_15, x_10, x_80);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_unbox(x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_85 = x_3;
x_86 = x_4;
x_87 = x_5;
x_88 = x_6;
x_89 = x_7;
x_90 = x_8;
x_91 = x_9;
x_92 = x_10;
x_93 = x_11;
x_94 = x_118;
goto block_111;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_120 = x_115;
} else {
 lean_dec_ref(x_115);
 x_120 = lean_box(0);
}
x_121 = lean_mk_string_unchecked("mkChainResultCore tac1", 22, 22);
x_122 = l_Lean_stringToMessageData(x_121);
lean_dec(x_121);
lean_inc(x_1);
x_123 = l_Lean_MessageData_ofSyntax(x_1);
x_124 = l_Lean_indentD(x_123);
if (lean_is_scalar(x_120)) {
 x_125 = lean_alloc_ctor(7, 2, 0);
} else {
 x_125 = x_120;
 lean_ctor_set_tag(x_125, 7);
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_mk_string_unchecked("", 0, 0);
x_127 = l_Lean_stringToMessageData(x_126);
lean_dec(x_126);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_127);
lean_inc(x_15);
x_129 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_15, x_128, x_8, x_9, x_10, x_11, x_119);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_85 = x_3;
x_86 = x_4;
x_87 = x_5;
x_88 = x_6;
x_89 = x_7;
x_90 = x_8;
x_91 = x_9;
x_92 = x_10;
x_93 = x_11;
x_94 = x_130;
goto block_111;
}
}
block_111:
{
size_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_95 = lean_array_size(x_84);
x_96 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__12(x_84, x_95, x_83, x_82, x_85, x_86, x_87, x_88, x_89, x_90, x_91, x_92, x_93, x_94);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
lean_inc(x_15);
x_98 = l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg(x_15, x_92, x_97);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_unbox(x_99);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_15);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_box(0);
x_103 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lam__0(x_82, x_84, x_1, x_83, x_13, x_14, x_2, x_102, x_85, x_86, x_87, x_88, x_89, x_90, x_91, x_92, x_93, x_101);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
lean_dec(x_98);
x_105 = lean_mk_string_unchecked("mkChainResult -----", 19, 19);
x_106 = l_Lean_stringToMessageData(x_105);
lean_dec(x_105);
x_107 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_15, x_106, x_90, x_91, x_92, x_93, x_104);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_box(0);
x_110 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lam__0(x_82, x_84, x_1, x_83, x_13, x_14, x_2, x_109, x_85, x_86, x_87, x_88, x_89, x_90, x_91, x_92, x_93, x_108);
return x_110;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__2___redArg(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_18 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__2(x_1, x_2, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__3(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_18 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_19 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__4(x_1, x_2, x_3, x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__5_spec__5(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__5(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__7(x_6, x_7, x_3, x_8, x_9);
lean_dec(x_3);
x_11 = lean_box(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__8(x_5, x_2, x_6, x_7);
lean_dec(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__10_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__10_spec__10(x_1, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__10(x_1, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__12_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__12_spec__12(x_1, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__12(x_1, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lam__0___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
_start:
{
size_t x_19; lean_object* x_20; 
x_19 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_20 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lam__0(x_1, x_2, x_3, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace_spec__0___redArg(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Parser", 6, 6);
x_14 = lean_mk_string_unchecked("Tactic", 6, 6);
x_15 = lean_mk_string_unchecked("grindTrace", 10, 10);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_16 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_15);
lean_inc(x_1);
x_17 = l_Lean_Syntax_isOfKind(x_1, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace_spec__0___redArg(x_11);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = lean_mk_string_unchecked("optConfig", 9, 9);
x_22 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_21);
lean_inc(x_20);
x_23 = l_Lean_Syntax_isOfKind(x_20, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace_spec__0___redArg(x_11);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_160; uint8_t x_161; 
x_25 = lean_unsigned_to_nat(2u);
x_160 = l_Lean_Syntax_getArg(x_1, x_25);
x_161 = l_Lean_Syntax_isNone(x_160);
if (x_161 == 0)
{
uint8_t x_162; 
lean_inc(x_160);
x_162 = l_Lean_Syntax_matchesNull(x_160, x_19);
if (x_162 == 0)
{
lean_object* x_163; 
lean_dec(x_160);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_163 = l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace_spec__0___redArg(x_11);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_unsigned_to_nat(0u);
x_165 = l_Lean_Syntax_getArg(x_160, x_164);
lean_dec(x_160);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_165);
x_139 = x_166;
x_140 = x_2;
x_141 = x_3;
x_142 = x_4;
x_143 = x_5;
x_144 = x_6;
x_145 = x_7;
x_146 = x_8;
x_147 = x_9;
x_148 = x_10;
x_149 = x_11;
goto block_159;
}
}
else
{
lean_object* x_167; 
lean_dec(x_160);
x_167 = lean_box(0);
x_139 = x_167;
x_140 = x_2;
x_141 = x_3;
x_142 = x_4;
x_143 = x_5;
x_144 = x_6;
x_145 = x_7;
x_146 = x_8;
x_147 = x_9;
x_148 = x_10;
x_149 = x_11;
goto block_159;
}
block_46:
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_30, 1);
x_37 = lean_ctor_get_uint8(x_36, sizeof(void*)*1 + 4);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; 
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
x_39 = l_Lean_Elab_Tactic_mkGrindOnly(x_26, x_29, x_27, x_31, x_32, x_33, x_34, x_35);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_mk_empty_array_with_capacity(x_25);
x_43 = lean_array_push(x_42, x_28);
x_44 = lean_array_push(x_43, x_40);
x_45 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg(x_44, x_31, x_32, x_33, x_34, x_41);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_44);
return x_45;
}
else
{
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_28);
return x_39;
}
}
}
block_117:
{
lean_object* x_60; 
lean_inc(x_58);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_20);
x_60 = l_Lean_Elab_Tactic_elabGrindConfig___redArg(x_20, x_51, x_53, x_54, x_55, x_56, x_57, x_58, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___redArg(x_1, x_57, x_58, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; lean_object* x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_50, 1);
x_67 = lean_ctor_get_uint8(x_66, sizeof(void*)*1 + 4);
x_68 = lean_ctor_get(x_61, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_61, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_61, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_61, 3);
lean_inc(x_71);
x_72 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 1);
x_73 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 2);
x_74 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 3);
x_75 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 4);
x_76 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 5);
x_77 = lean_ctor_get(x_61, 4);
lean_inc(x_77);
x_78 = lean_ctor_get(x_61, 5);
lean_inc(x_78);
x_79 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 6);
x_80 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 7);
x_81 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 8);
x_82 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 9);
x_83 = lean_box(0);
x_84 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 11);
x_85 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 12);
x_86 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 13);
x_87 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 14);
x_88 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 15);
x_89 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 16);
x_90 = lean_ctor_get(x_61, 6);
lean_inc(x_90);
x_91 = lean_ctor_get_uint8(x_61, sizeof(void*)*7 + 17);
lean_dec(x_61);
x_92 = lean_alloc_ctor(0, 7, 18);
lean_ctor_set(x_92, 0, x_68);
lean_ctor_set(x_92, 1, x_69);
lean_ctor_set(x_92, 2, x_70);
lean_ctor_set(x_92, 3, x_71);
lean_ctor_set(x_92, 4, x_77);
lean_ctor_set(x_92, 5, x_78);
lean_ctor_set(x_92, 6, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*7, x_67);
lean_ctor_set_uint8(x_92, sizeof(void*)*7 + 1, x_72);
lean_ctor_set_uint8(x_92, sizeof(void*)*7 + 2, x_73);
lean_ctor_set_uint8(x_92, sizeof(void*)*7 + 3, x_74);
lean_ctor_set_uint8(x_92, sizeof(void*)*7 + 4, x_75);
lean_ctor_set_uint8(x_92, sizeof(void*)*7 + 5, x_76);
lean_ctor_set_uint8(x_92, sizeof(void*)*7 + 6, x_79);
lean_ctor_set_uint8(x_92, sizeof(void*)*7 + 7, x_80);
lean_ctor_set_uint8(x_92, sizeof(void*)*7 + 8, x_81);
lean_ctor_set_uint8(x_92, sizeof(void*)*7 + 9, x_82);
x_93 = lean_unbox(x_83);
lean_ctor_set_uint8(x_92, sizeof(void*)*7 + 10, x_93);
lean_ctor_set_uint8(x_92, sizeof(void*)*7 + 11, x_84);
lean_ctor_set_uint8(x_92, sizeof(void*)*7 + 12, x_85);
lean_ctor_set_uint8(x_92, sizeof(void*)*7 + 13, x_86);
lean_ctor_set_uint8(x_92, sizeof(void*)*7 + 14, x_87);
lean_ctor_set_uint8(x_92, sizeof(void*)*7 + 15, x_88);
lean_ctor_set_uint8(x_92, sizeof(void*)*7 + 16, x_89);
lean_ctor_set_uint8(x_92, sizeof(void*)*7 + 17, x_91);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_49);
x_94 = l_Lean_Elab_Tactic_evalGrindCore(x_64, x_92, x_48, x_47, x_49, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_65);
lean_dec(x_47);
lean_dec(x_48);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_mk_string_unchecked("try", 3, 3);
x_98 = lean_mk_string_unchecked("debug", 5, 5);
x_99 = l_Lean_Name_mkStr2(x_97, x_98);
lean_inc(x_99);
x_100 = l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg(x_99, x_57, x_96);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_unbox(x_101);
lean_dec(x_101);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec(x_99);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
x_26 = x_20;
x_27 = x_95;
x_28 = x_64;
x_29 = x_49;
x_30 = x_50;
x_31 = x_55;
x_32 = x_56;
x_33 = x_57;
x_34 = x_58;
x_35 = x_103;
goto block_46;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
lean_dec(x_100);
x_105 = lean_mk_string_unchecked("`grind` succeeded", 17, 17);
x_106 = l_Lean_stringToMessageData(x_105);
lean_dec(x_105);
x_107 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_99, x_106, x_55, x_56, x_57, x_58, x_104);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_26 = x_20;
x_27 = x_95;
x_28 = x_64;
x_29 = x_49;
x_30 = x_50;
x_31 = x_55;
x_32 = x_56;
x_33 = x_57;
x_34 = x_58;
x_35 = x_108;
goto block_46;
}
}
else
{
uint8_t x_109; 
lean_dec(x_64);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_49);
lean_dec(x_20);
x_109 = !lean_is_exclusive(x_94);
if (x_109 == 0)
{
return x_94;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_94, 0);
x_111 = lean_ctor_get(x_94, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_94);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_20);
return x_63;
}
}
else
{
uint8_t x_113; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_20);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_60);
if (x_113 == 0)
{
return x_60;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_60, 0);
x_115 = lean_ctor_get(x_60, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_60);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
block_138:
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = lean_unsigned_to_nat(4u);
x_131 = l_Lean_Syntax_getArg(x_1, x_130);
x_132 = l_Lean_Syntax_isNone(x_131);
if (x_132 == 0)
{
uint8_t x_133; 
lean_inc(x_131);
x_133 = l_Lean_Syntax_matchesNull(x_131, x_25);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec(x_131);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_20);
lean_dec(x_1);
x_134 = l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace_spec__0___redArg(x_129);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = l_Lean_Syntax_getArg(x_131, x_19);
lean_dec(x_131);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_47 = x_119;
x_48 = x_118;
x_49 = x_136;
x_50 = x_120;
x_51 = x_121;
x_52 = x_122;
x_53 = x_123;
x_54 = x_124;
x_55 = x_125;
x_56 = x_126;
x_57 = x_127;
x_58 = x_128;
x_59 = x_129;
goto block_117;
}
}
else
{
lean_object* x_137; 
lean_dec(x_131);
x_137 = lean_box(0);
x_47 = x_119;
x_48 = x_118;
x_49 = x_137;
x_50 = x_120;
x_51 = x_121;
x_52 = x_122;
x_53 = x_123;
x_54 = x_124;
x_55 = x_125;
x_56 = x_126;
x_57 = x_127;
x_58 = x_128;
x_59 = x_129;
goto block_117;
}
}
block_159:
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_150 = lean_unsigned_to_nat(3u);
x_151 = l_Lean_Syntax_getArg(x_1, x_150);
x_152 = l_Lean_Syntax_isNone(x_151);
if (x_152 == 0)
{
uint8_t x_153; 
lean_inc(x_151);
x_153 = l_Lean_Syntax_matchesNull(x_151, x_150);
if (x_153 == 0)
{
lean_object* x_154; 
lean_dec(x_151);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_20);
lean_dec(x_1);
x_154 = l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace_spec__0___redArg(x_149);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = l_Lean_Syntax_getArg(x_151, x_19);
lean_dec(x_151);
x_156 = l_Lean_Syntax_getArgs(x_155);
lean_dec(x_155);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_156);
x_118 = x_139;
x_119 = x_157;
x_120 = x_140;
x_121 = x_141;
x_122 = x_142;
x_123 = x_143;
x_124 = x_144;
x_125 = x_145;
x_126 = x_146;
x_127 = x_147;
x_128 = x_148;
x_129 = x_149;
goto block_138;
}
}
else
{
lean_object* x_158; 
lean_dec(x_151);
x_158 = lean_box(0);
x_118 = x_139;
x_119 = x_158;
x_120 = x_140;
x_121 = x_141;
x_122 = x_142;
x_123 = x_143;
x_124 = x_144;
x_125 = x_145;
x_126 = x_146;
x_127 = x_147;
x_128 = x_148;
x_129 = x_149;
goto block_138;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace_spec__0___redArg___lam__0), 11, 6);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_4);
lean_closure_set(x_13, 3, x_5);
lean_closure_set(x_13, 4, x_6);
lean_closure_set(x_13, 5, x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_13, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
return x_14;
}
else
{
uint8_t x_15; 
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
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lam__0(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (x_1 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace_spec__0___redArg(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_2, x_19);
x_21 = l_Lean_Syntax_matchesNull(x_20, x_18);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace_spec__0___redArg(x_16);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_23 = lean_unsigned_to_nat(2u);
x_114 = l_Lean_Syntax_getArg(x_2, x_23);
x_154 = lean_mk_string_unchecked("simpTraceArgsRest", 17, 17);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_155 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_154);
lean_inc(x_114);
x_156 = l_Lean_Syntax_isOfKind(x_114, x_155);
lean_dec(x_155);
if (x_156 == 0)
{
lean_object* x_157; 
lean_dec(x_114);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_157 = l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace_spec__0___redArg(x_16);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_158 = l_Lean_Syntax_getArg(x_114, x_18);
x_159 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_160 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_159);
x_161 = l_Lean_Syntax_isOfKind(x_158, x_160);
lean_dec(x_160);
if (x_161 == 0)
{
lean_object* x_162; 
lean_dec(x_114);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_162 = l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace_spec__0___redArg(x_16);
return x_162;
}
else
{
lean_object* x_163; uint8_t x_164; 
x_163 = l_Lean_Syntax_getArg(x_114, x_19);
x_164 = l_Lean_Syntax_matchesNull(x_163, x_18);
if (x_164 == 0)
{
lean_object* x_165; 
lean_dec(x_114);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_165 = l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace_spec__0___redArg(x_16);
return x_165;
}
else
{
lean_object* x_166; uint8_t x_167; 
x_166 = l_Lean_Syntax_getArg(x_114, x_23);
x_167 = l_Lean_Syntax_isNone(x_166);
if (x_167 == 0)
{
uint8_t x_168; 
x_168 = l_Lean_Syntax_matchesNull(x_166, x_19);
if (x_168 == 0)
{
lean_object* x_169; 
lean_dec(x_114);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_169 = l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace_spec__0___redArg(x_16);
return x_169;
}
else
{
x_133 = x_7;
x_134 = x_8;
x_135 = x_9;
x_136 = x_10;
x_137 = x_11;
x_138 = x_12;
x_139 = x_13;
x_140 = x_14;
x_141 = x_15;
x_142 = x_16;
goto block_153;
}
}
else
{
lean_dec(x_166);
x_133 = x_7;
x_134 = x_8;
x_135 = x_9;
x_136 = x_10;
x_137 = x_11;
x_138 = x_12;
x_139 = x_13;
x_140 = x_14;
x_141 = x_15;
x_142 = x_16;
goto block_153;
}
}
}
}
block_43:
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_26, 1);
x_33 = lean_ctor_get_uint8(x_32, sizeof(void*)*1 + 4);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_24, 0);
lean_inc(x_35);
lean_dec(x_24);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_25);
x_36 = l_Lean_Elab_Tactic_mkSimpCallStx(x_25, x_35, x_27, x_28, x_29, x_30, x_31);
lean_dec(x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_mk_empty_array_with_capacity(x_23);
x_40 = lean_array_push(x_39, x_25);
x_41 = lean_array_push(x_40, x_37);
x_42 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg(x_41, x_27, x_28, x_29, x_30, x_38);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_41);
return x_42;
}
else
{
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
return x_36;
}
}
}
block_78:
{
lean_object* x_59; 
lean_inc(x_57);
lean_inc(x_54);
lean_inc(x_53);
x_59 = l_Lean_Elab_Tactic_simpLocation(x_50, x_48, x_45, x_58, x_52, x_46, x_55, x_44, x_47, x_53, x_54, x_57, x_49);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_mk_string_unchecked("try", 3, 3);
x_63 = lean_mk_string_unchecked("debug", 5, 5);
x_64 = l_Lean_Name_mkStr2(x_62, x_63);
lean_inc(x_64);
x_65 = l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg(x_64, x_54, x_61);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_unbox(x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_64);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_24 = x_60;
x_25 = x_56;
x_26 = x_51;
x_27 = x_47;
x_28 = x_53;
x_29 = x_54;
x_30 = x_57;
x_31 = x_68;
goto block_43;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_dec(x_65);
x_70 = lean_mk_string_unchecked("`simp` succeeded", 16, 16);
x_71 = l_Lean_stringToMessageData(x_70);
lean_dec(x_70);
x_72 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_64, x_71, x_47, x_53, x_54, x_57, x_69);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_24 = x_60;
x_25 = x_56;
x_26 = x_51;
x_27 = x_47;
x_28 = x_53;
x_29 = x_54;
x_30 = x_57;
x_31 = x_73;
goto block_43;
}
}
else
{
uint8_t x_74; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_47);
x_74 = !lean_is_exclusive(x_59);
if (x_74 == 0)
{
return x_59;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_59, 0);
x_76 = lean_ctor_get(x_59, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_59);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
block_113:
{
lean_object* x_90; 
x_90 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___redArg(x_2, x_85, x_88, x_87);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; lean_object* x_99; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_box(0);
x_94 = lean_box(0);
x_95 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpTheorems___boxed), 3, 0);
x_96 = lean_unbox(x_93);
x_97 = lean_unbox(x_94);
x_98 = lean_unbox(x_93);
lean_inc(x_88);
lean_inc(x_85);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_79);
lean_inc(x_86);
lean_inc(x_81);
lean_inc(x_84);
x_99 = l_Lean_Elab_Tactic_mkSimpContext(x_91, x_96, x_97, x_98, x_95, x_84, x_81, x_86, x_79, x_82, x_83, x_85, x_88, x_92);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
x_104 = lean_box(0);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_mk_empty_array_with_capacity(x_18);
x_106 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set_uint8(x_106, sizeof(void*)*1, x_3);
x_44 = x_79;
x_45 = x_104;
x_46 = x_81;
x_47 = x_82;
x_48 = x_103;
x_49 = x_101;
x_50 = x_102;
x_51 = x_80;
x_52 = x_84;
x_53 = x_83;
x_54 = x_85;
x_55 = x_86;
x_56 = x_91;
x_57 = x_88;
x_58 = x_106;
goto block_78;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_89, 0);
lean_inc(x_107);
lean_dec(x_89);
x_108 = l_Lean_Elab_Tactic_expandLocation(x_107);
lean_dec(x_107);
x_44 = x_79;
x_45 = x_104;
x_46 = x_81;
x_47 = x_82;
x_48 = x_103;
x_49 = x_101;
x_50 = x_102;
x_51 = x_80;
x_52 = x_84;
x_53 = x_83;
x_54 = x_85;
x_55 = x_86;
x_56 = x_91;
x_57 = x_88;
x_58 = x_108;
goto block_78;
}
}
else
{
uint8_t x_109; 
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_79);
x_109 = !lean_is_exclusive(x_99);
if (x_109 == 0)
{
return x_99;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_99, 0);
x_111 = lean_ctor_get(x_99, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_99);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_79);
return x_90;
}
}
block_132:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_unsigned_to_nat(4u);
x_126 = l_Lean_Syntax_getArg(x_114, x_125);
lean_dec(x_114);
x_127 = l_Lean_Syntax_getOptional_x3f(x_126);
lean_dec(x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_box(0);
x_79 = x_119;
x_80 = x_115;
x_81 = x_117;
x_82 = x_120;
x_83 = x_121;
x_84 = x_116;
x_85 = x_122;
x_86 = x_118;
x_87 = x_124;
x_88 = x_123;
x_89 = x_128;
goto block_113;
}
else
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_127);
if (x_129 == 0)
{
x_79 = x_119;
x_80 = x_115;
x_81 = x_117;
x_82 = x_120;
x_83 = x_121;
x_84 = x_116;
x_85 = x_122;
x_86 = x_118;
x_87 = x_124;
x_88 = x_123;
x_89 = x_127;
goto block_113;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_79 = x_119;
x_80 = x_115;
x_81 = x_117;
x_82 = x_120;
x_83 = x_121;
x_84 = x_116;
x_85 = x_122;
x_86 = x_118;
x_87 = x_124;
x_88 = x_123;
x_89 = x_131;
goto block_113;
}
}
}
block_153:
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_143 = lean_unsigned_to_nat(3u);
x_144 = l_Lean_Syntax_getArg(x_114, x_143);
x_145 = l_Lean_Syntax_isNone(x_144);
if (x_145 == 0)
{
uint8_t x_146; 
lean_inc(x_144);
x_146 = l_Lean_Syntax_matchesNull(x_144, x_19);
if (x_146 == 0)
{
lean_object* x_147; 
lean_dec(x_144);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_114);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_147 = l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace_spec__0___redArg(x_142);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_148 = l_Lean_Syntax_getArg(x_144, x_18);
lean_dec(x_144);
x_149 = lean_mk_string_unchecked("simpArgs", 8, 8);
x_150 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_149);
x_151 = l_Lean_Syntax_isOfKind(x_148, x_150);
lean_dec(x_150);
if (x_151 == 0)
{
lean_object* x_152; 
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_114);
lean_dec(x_2);
x_152 = l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace_spec__0___redArg(x_142);
return x_152;
}
else
{
x_115 = x_133;
x_116 = x_134;
x_117 = x_135;
x_118 = x_136;
x_119 = x_137;
x_120 = x_138;
x_121 = x_139;
x_122 = x_140;
x_123 = x_141;
x_124 = x_142;
goto block_132;
}
}
}
else
{
lean_dec(x_144);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_115 = x_133;
x_116 = x_134;
x_117 = x_135;
x_118 = x_136;
x_119 = x_137;
x_120 = x_138;
x_121 = x_139;
x_122 = x_140;
x_123 = x_141;
x_124 = x_142;
goto block_132;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_mk_string_unchecked("Lean", 4, 4);
x_16 = lean_mk_string_unchecked("Parser", 6, 6);
x_17 = lean_mk_string_unchecked("Tactic", 6, 6);
x_18 = lean_mk_string_unchecked("simpTrace", 9, 9);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_19 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_18);
lean_inc(x_1);
x_20 = l_Lean_Syntax_isOfKind(x_1, x_19);
lean_dec(x_19);
x_21 = lean_box(1);
x_22 = lean_box(x_20);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lam__0___boxed), 16, 6);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_1);
lean_closure_set(x_23, 2, x_21);
lean_closure_set(x_23, 3, x_15);
lean_closure_set(x_23, 4, x_16);
lean_closure_set(x_23, 5, x_17);
x_24 = l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace_spec__0___redArg(x_13, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_1);
lean_dec(x_1);
x_18 = lean_unbox(x_3);
lean_dec(x_3);
x_19 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lam__0(x_17, x_2, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_eval_suggest_tactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_34; lean_object* x_42; lean_object* x_43; 
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_box(0);
lean_ctor_set(x_2, 1, x_17);
x_18 = l_Lean_Elab_Tactic_setGoals___redArg(x_2, x_6, x_13);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Elab_Tactic_saveState___redArg(x_6, x_8, x_10, x_11, x_12, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_1);
x_42 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_evalSuggest___boxed), 11, 2);
lean_closure_set(x_42, 0, x_1);
lean_closure_set(x_42, 1, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_Lean_Elab_Tactic_withoutRecover(lean_box(0), x_42, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_22);
if (lean_obj_tag(x_43) == 0)
{
lean_dec(x_21);
x_34 = x_43;
goto block_41;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_80; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
x_80 = l_Lean_Exception_isInterrupt(x_44);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = l_Lean_Exception_isRuntime(x_44);
lean_dec(x_44);
x_46 = x_81;
goto block_79;
}
else
{
lean_dec(x_44);
x_46 = x_80;
goto block_79;
}
block_79:
{
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_43);
x_47 = l_Lean_Elab_Tactic_SavedState_restore(x_21, x_46, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_45);
x_48 = lean_ctor_get(x_4, 1);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_48, sizeof(void*)*1 + 3);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_mk_string_unchecked("failed", 6, 6);
x_52 = l_Lean_stringToMessageData(x_51);
lean_dec(x_51);
x_53 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_52, x_9, x_10, x_11, x_12, x_50);
x_34 = x_53;
goto block_41;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_st_ref_get(x_12, x_54);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_57 = lean_ctor_get(x_55, 1);
x_58 = lean_ctor_get(x_55, 0);
lean_dec(x_58);
x_59 = lean_ctor_get(x_11, 5);
lean_inc(x_59);
x_60 = l_Lean_SourceInfo_fromRef(x_59, x_46);
lean_dec(x_59);
x_61 = lean_mk_string_unchecked("Lean", 4, 4);
x_62 = lean_mk_string_unchecked("Parser", 6, 6);
x_63 = lean_mk_string_unchecked("Tactic", 6, 6);
x_64 = lean_mk_string_unchecked("tacticSorry", 11, 11);
x_65 = l_Lean_Name_mkStr4(x_61, x_62, x_63, x_64);
x_66 = lean_mk_string_unchecked("sorry", 5, 5);
lean_inc(x_60);
lean_ctor_set_tag(x_55, 2);
lean_ctor_set(x_55, 1, x_66);
lean_ctor_set(x_55, 0, x_60);
x_67 = l_Lean_Syntax_node1(x_60, x_65, x_55);
x_26 = x_67;
x_27 = x_57;
goto block_33;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_68 = lean_ctor_get(x_55, 1);
lean_inc(x_68);
lean_dec(x_55);
x_69 = lean_ctor_get(x_11, 5);
lean_inc(x_69);
x_70 = l_Lean_SourceInfo_fromRef(x_69, x_46);
lean_dec(x_69);
x_71 = lean_mk_string_unchecked("Lean", 4, 4);
x_72 = lean_mk_string_unchecked("Parser", 6, 6);
x_73 = lean_mk_string_unchecked("Tactic", 6, 6);
x_74 = lean_mk_string_unchecked("tacticSorry", 11, 11);
x_75 = l_Lean_Name_mkStr4(x_71, x_72, x_73, x_74);
x_76 = lean_mk_string_unchecked("sorry", 5, 5);
lean_inc(x_70);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_70);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Syntax_node1(x_70, x_75, x_77);
x_26 = x_78;
x_27 = x_68;
goto block_33;
}
}
}
else
{
lean_dec(x_45);
lean_dec(x_21);
x_34 = x_43;
goto block_41;
}
}
}
block_33:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_24, x_28);
lean_dec(x_24);
x_30 = lean_array_push(x_25, x_26);
if (lean_is_scalar(x_23)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_23;
}
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_2 = x_16;
x_3 = x_31;
x_13 = x_27;
goto _start;
}
block_41:
{
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_26 = x_35;
x_27 = x_36;
goto block_33;
}
else
{
uint8_t x_37; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_102; lean_object* x_110; lean_object* x_111; 
x_82 = lean_ctor_get(x_2, 0);
x_83 = lean_ctor_get(x_2, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_2);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_Elab_Tactic_setGoals___redArg(x_85, x_6, x_13);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = l_Lean_Elab_Tactic_saveState___redArg(x_6, x_8, x_10, x_11, x_12, x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_3, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_3, 1);
lean_inc(x_93);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_1);
x_110 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_evalSuggest___boxed), 11, 2);
lean_closure_set(x_110, 0, x_1);
lean_closure_set(x_110, 1, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_111 = l_Lean_Elab_Tactic_withoutRecover(lean_box(0), x_110, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_90);
if (lean_obj_tag(x_111) == 0)
{
lean_dec(x_89);
x_102 = x_111;
goto block_109;
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_137; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
x_137 = l_Lean_Exception_isInterrupt(x_112);
if (x_137 == 0)
{
uint8_t x_138; 
x_138 = l_Lean_Exception_isRuntime(x_112);
lean_dec(x_112);
x_114 = x_138;
goto block_136;
}
else
{
lean_dec(x_112);
x_114 = x_137;
goto block_136;
}
block_136:
{
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_dec(x_111);
x_115 = l_Lean_Elab_Tactic_SavedState_restore(x_89, x_114, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_113);
x_116 = lean_ctor_get(x_4, 1);
lean_inc(x_116);
x_117 = lean_ctor_get_uint8(x_116, sizeof(void*)*1 + 3);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_119 = lean_mk_string_unchecked("failed", 6, 6);
x_120 = l_Lean_stringToMessageData(x_119);
lean_dec(x_119);
x_121 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_120, x_9, x_10, x_11, x_12, x_118);
x_102 = x_121;
goto block_109;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_122 = lean_ctor_get(x_115, 1);
lean_inc(x_122);
lean_dec(x_115);
x_123 = lean_st_ref_get(x_12, x_122);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_125 = x_123;
} else {
 lean_dec_ref(x_123);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_11, 5);
lean_inc(x_126);
x_127 = l_Lean_SourceInfo_fromRef(x_126, x_114);
lean_dec(x_126);
x_128 = lean_mk_string_unchecked("Lean", 4, 4);
x_129 = lean_mk_string_unchecked("Parser", 6, 6);
x_130 = lean_mk_string_unchecked("Tactic", 6, 6);
x_131 = lean_mk_string_unchecked("tacticSorry", 11, 11);
x_132 = l_Lean_Name_mkStr4(x_128, x_129, x_130, x_131);
x_133 = lean_mk_string_unchecked("sorry", 5, 5);
lean_inc(x_127);
if (lean_is_scalar(x_125)) {
 x_134 = lean_alloc_ctor(2, 2, 0);
} else {
 x_134 = x_125;
 lean_ctor_set_tag(x_134, 2);
}
lean_ctor_set(x_134, 0, x_127);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_Syntax_node1(x_127, x_132, x_134);
x_94 = x_135;
x_95 = x_124;
goto block_101;
}
}
else
{
lean_dec(x_113);
lean_dec(x_89);
x_102 = x_111;
goto block_109;
}
}
}
block_101:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_add(x_92, x_96);
lean_dec(x_92);
x_98 = lean_array_push(x_93, x_94);
if (lean_is_scalar(x_91)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_91;
}
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_2 = x_83;
x_3 = x_99;
x_13 = x_95;
goto _start;
}
block_109:
{
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_94 = x_103;
x_95 = x_104;
goto block_101;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_83);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_105 = lean_ctor_get(x_102, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_102, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_107 = x_102;
} else {
 lean_dec_ref(x_102);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0_spec__0___redArg(x_1, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_35; lean_object* x_43; lean_object* x_44; 
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_box(0);
lean_ctor_set(x_3, 1, x_18);
x_19 = l_Lean_Elab_Tactic_setGoals___redArg(x_3, x_7, x_14);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Elab_Tactic_saveState___redArg(x_7, x_9, x_11, x_12, x_13, x_20);
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
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_dec(x_4);
lean_inc(x_5);
lean_inc(x_1);
x_43 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_evalSuggest___boxed), 11, 2);
lean_closure_set(x_43, 0, x_1);
lean_closure_set(x_43, 1, x_5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_44 = l_Lean_Elab_Tactic_withoutRecover(lean_box(0), x_43, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_23);
if (lean_obj_tag(x_44) == 0)
{
lean_dec(x_22);
x_35 = x_44;
goto block_42;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_81; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
x_81 = l_Lean_Exception_isInterrupt(x_45);
if (x_81 == 0)
{
uint8_t x_82; 
x_82 = l_Lean_Exception_isRuntime(x_45);
lean_dec(x_45);
x_47 = x_82;
goto block_80;
}
else
{
lean_dec(x_45);
x_47 = x_81;
goto block_80;
}
block_80:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_44);
x_48 = l_Lean_Elab_Tactic_SavedState_restore(x_22, x_47, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_46);
x_49 = lean_ctor_get(x_5, 1);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_49, sizeof(void*)*1 + 3);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_mk_string_unchecked("failed", 6, 6);
x_53 = l_Lean_stringToMessageData(x_52);
lean_dec(x_52);
x_54 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_53, x_10, x_11, x_12, x_13, x_51);
x_35 = x_54;
goto block_42;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_st_ref_get(x_13, x_55);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_58 = lean_ctor_get(x_56, 1);
x_59 = lean_ctor_get(x_56, 0);
lean_dec(x_59);
x_60 = lean_ctor_get(x_12, 5);
lean_inc(x_60);
x_61 = l_Lean_SourceInfo_fromRef(x_60, x_47);
lean_dec(x_60);
x_62 = lean_mk_string_unchecked("Lean", 4, 4);
x_63 = lean_mk_string_unchecked("Parser", 6, 6);
x_64 = lean_mk_string_unchecked("Tactic", 6, 6);
x_65 = lean_mk_string_unchecked("tacticSorry", 11, 11);
x_66 = l_Lean_Name_mkStr4(x_62, x_63, x_64, x_65);
x_67 = lean_mk_string_unchecked("sorry", 5, 5);
lean_inc(x_61);
lean_ctor_set_tag(x_56, 2);
lean_ctor_set(x_56, 1, x_67);
lean_ctor_set(x_56, 0, x_61);
x_68 = l_Lean_Syntax_node1(x_61, x_66, x_56);
x_27 = x_68;
x_28 = x_58;
goto block_34;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_69 = lean_ctor_get(x_56, 1);
lean_inc(x_69);
lean_dec(x_56);
x_70 = lean_ctor_get(x_12, 5);
lean_inc(x_70);
x_71 = l_Lean_SourceInfo_fromRef(x_70, x_47);
lean_dec(x_70);
x_72 = lean_mk_string_unchecked("Lean", 4, 4);
x_73 = lean_mk_string_unchecked("Parser", 6, 6);
x_74 = lean_mk_string_unchecked("Tactic", 6, 6);
x_75 = lean_mk_string_unchecked("tacticSorry", 11, 11);
x_76 = l_Lean_Name_mkStr4(x_72, x_73, x_74, x_75);
x_77 = lean_mk_string_unchecked("sorry", 5, 5);
lean_inc(x_71);
x_78 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_Syntax_node1(x_71, x_76, x_78);
x_27 = x_79;
x_28 = x_69;
goto block_34;
}
}
}
else
{
lean_dec(x_46);
lean_dec(x_22);
x_35 = x_44;
goto block_42;
}
}
}
block_34:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_25, x_29);
lean_dec(x_25);
x_31 = lean_array_push(x_26, x_27);
if (lean_is_scalar(x_24)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_24;
}
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0_spec__0___redArg(x_1, x_17, x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_28);
return x_33;
}
block_42:
{
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_27 = x_36;
x_28 = x_37;
goto block_34;
}
else
{
uint8_t x_38; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
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
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_103; lean_object* x_111; lean_object* x_112; 
x_83 = lean_ctor_get(x_3, 0);
x_84 = lean_ctor_get(x_3, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_3);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_Elab_Tactic_setGoals___redArg(x_86, x_7, x_14);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = l_Lean_Elab_Tactic_saveState___redArg(x_7, x_9, x_11, x_12, x_13, x_88);
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
x_93 = lean_ctor_get(x_4, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_4, 1);
lean_inc(x_94);
lean_dec(x_4);
lean_inc(x_5);
lean_inc(x_1);
x_111 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_evalSuggest___boxed), 11, 2);
lean_closure_set(x_111, 0, x_1);
lean_closure_set(x_111, 1, x_5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_112 = l_Lean_Elab_Tactic_withoutRecover(lean_box(0), x_111, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_91);
if (lean_obj_tag(x_112) == 0)
{
lean_dec(x_90);
x_103 = x_112;
goto block_110;
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_138; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
x_138 = l_Lean_Exception_isInterrupt(x_113);
if (x_138 == 0)
{
uint8_t x_139; 
x_139 = l_Lean_Exception_isRuntime(x_113);
lean_dec(x_113);
x_115 = x_139;
goto block_137;
}
else
{
lean_dec(x_113);
x_115 = x_138;
goto block_137;
}
block_137:
{
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
lean_dec(x_112);
x_116 = l_Lean_Elab_Tactic_SavedState_restore(x_90, x_115, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_114);
x_117 = lean_ctor_get(x_5, 1);
lean_inc(x_117);
x_118 = lean_ctor_get_uint8(x_117, sizeof(void*)*1 + 3);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
lean_dec(x_116);
x_120 = lean_mk_string_unchecked("failed", 6, 6);
x_121 = l_Lean_stringToMessageData(x_120);
lean_dec(x_120);
x_122 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_121, x_10, x_11, x_12, x_13, x_119);
x_103 = x_122;
goto block_110;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_123 = lean_ctor_get(x_116, 1);
lean_inc(x_123);
lean_dec(x_116);
x_124 = lean_st_ref_get(x_13, x_123);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_126 = x_124;
} else {
 lean_dec_ref(x_124);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_12, 5);
lean_inc(x_127);
x_128 = l_Lean_SourceInfo_fromRef(x_127, x_115);
lean_dec(x_127);
x_129 = lean_mk_string_unchecked("Lean", 4, 4);
x_130 = lean_mk_string_unchecked("Parser", 6, 6);
x_131 = lean_mk_string_unchecked("Tactic", 6, 6);
x_132 = lean_mk_string_unchecked("tacticSorry", 11, 11);
x_133 = l_Lean_Name_mkStr4(x_129, x_130, x_131, x_132);
x_134 = lean_mk_string_unchecked("sorry", 5, 5);
lean_inc(x_128);
if (lean_is_scalar(x_126)) {
 x_135 = lean_alloc_ctor(2, 2, 0);
} else {
 x_135 = x_126;
 lean_ctor_set_tag(x_135, 2);
}
lean_ctor_set(x_135, 0, x_128);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Lean_Syntax_node1(x_128, x_133, x_135);
x_95 = x_136;
x_96 = x_125;
goto block_102;
}
}
else
{
lean_dec(x_114);
lean_dec(x_90);
x_103 = x_112;
goto block_110;
}
}
}
block_102:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_add(x_93, x_97);
lean_dec(x_93);
x_99 = lean_array_push(x_94, x_95);
if (lean_is_scalar(x_92)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_92;
}
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0_spec__0___redArg(x_1, x_84, x_100, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_96);
return x_101;
}
block_110:
{
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_95 = x_104;
x_96 = x_105;
goto block_102;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_84);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_106 = lean_ctor_get(x_103, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_103, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_108 = x_103;
} else {
 lean_dec_ref(x_103);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(x_2, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__3(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_box(1);
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_unbox(x_5);
return x_8;
}
else
{
if (x_4 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = lean_unbox(x_5);
return x_13;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_33; 
x_33 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_mk_string_unchecked("invalid `<;>` occurrence in non-terminal position for `try\?` script", 67, 67);
x_35 = l_Lean_stringToMessageData(x_34);
lean_dec(x_34);
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
lean_dec(x_3);
x_37 = l_Lean_MessageData_ofSyntax(x_36);
x_38 = l_Lean_indentD(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_mk_string_unchecked("", 0, 0);
x_41 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(x_42, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_3, 0);
lean_inc(x_48);
x_49 = lean_box(0);
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
x_51 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_unbox(x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*2, x_52);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_53 = lean_eval_suggest_tactic(x_1, x_51, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Elab_Tactic_getGoals(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_box(0);
x_60 = l_Lean_Elab_Tactic_setGoals___redArg(x_59, x_5, x_58);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_60, 1);
x_63 = lean_ctor_get(x_60, 0);
lean_dec(x_63);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_mk_empty_array_with_capacity(x_64);
lean_ctor_set(x_60, 1, x_65);
lean_ctor_set(x_60, 0, x_64);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_57);
x_66 = l_List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0___redArg(x_2, x_57, x_57, x_60, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_62);
lean_dec(x_57);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_array_get_size(x_69);
x_71 = lean_nat_dec_lt(x_64, x_70);
if (x_71 == 0)
{
lean_dec(x_70);
x_13 = x_68;
x_14 = x_69;
x_15 = x_6;
x_16 = x_4;
x_17 = x_11;
x_18 = x_10;
x_19 = x_5;
x_20 = x_3;
x_21 = x_54;
x_22 = x_9;
x_23 = x_7;
x_24 = x_8;
goto block_32;
}
else
{
if (x_71 == 0)
{
lean_dec(x_70);
x_13 = x_68;
x_14 = x_69;
x_15 = x_6;
x_16 = x_4;
x_17 = x_11;
x_18 = x_10;
x_19 = x_5;
x_20 = x_3;
x_21 = x_54;
x_22 = x_9;
x_23 = x_7;
x_24 = x_8;
goto block_32;
}
else
{
size_t x_72; size_t x_73; uint8_t x_74; 
x_72 = lean_usize_of_nat(x_64);
x_73 = lean_usize_of_nat(x_70);
lean_dec(x_70);
x_74 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__3(x_69, x_72, x_73);
if (x_74 == 0)
{
x_13 = x_68;
x_14 = x_69;
x_15 = x_6;
x_16 = x_4;
x_17 = x_11;
x_18 = x_10;
x_19 = x_5;
x_20 = x_3;
x_21 = x_54;
x_22 = x_9;
x_23 = x_7;
x_24 = x_8;
goto block_32;
}
else
{
lean_object* x_75; 
x_75 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult(x_54, x_69, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_68);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_75;
}
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_54);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_76 = !lean_is_exclusive(x_66);
if (x_76 == 0)
{
return x_66;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_66, 0);
x_78 = lean_ctor_get(x_66, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_66);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_60, 1);
lean_inc(x_80);
lean_dec(x_60);
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_mk_empty_array_with_capacity(x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_57);
x_84 = l_List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0___redArg(x_2, x_57, x_57, x_83, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_80);
lean_dec(x_57);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_array_get_size(x_87);
x_89 = lean_nat_dec_lt(x_81, x_88);
if (x_89 == 0)
{
lean_dec(x_88);
x_13 = x_86;
x_14 = x_87;
x_15 = x_6;
x_16 = x_4;
x_17 = x_11;
x_18 = x_10;
x_19 = x_5;
x_20 = x_3;
x_21 = x_54;
x_22 = x_9;
x_23 = x_7;
x_24 = x_8;
goto block_32;
}
else
{
if (x_89 == 0)
{
lean_dec(x_88);
x_13 = x_86;
x_14 = x_87;
x_15 = x_6;
x_16 = x_4;
x_17 = x_11;
x_18 = x_10;
x_19 = x_5;
x_20 = x_3;
x_21 = x_54;
x_22 = x_9;
x_23 = x_7;
x_24 = x_8;
goto block_32;
}
else
{
size_t x_90; size_t x_91; uint8_t x_92; 
x_90 = lean_usize_of_nat(x_81);
x_91 = lean_usize_of_nat(x_88);
lean_dec(x_88);
x_92 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__3(x_87, x_90, x_91);
if (x_92 == 0)
{
x_13 = x_86;
x_14 = x_87;
x_15 = x_6;
x_16 = x_4;
x_17 = x_11;
x_18 = x_10;
x_19 = x_5;
x_20 = x_3;
x_21 = x_54;
x_22 = x_9;
x_23 = x_7;
x_24 = x_8;
goto block_32;
}
else
{
lean_object* x_93; 
x_93 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult(x_54, x_87, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_86);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_93;
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_54);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_94 = lean_ctor_get(x_84, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_84, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_96 = x_84;
} else {
 lean_dec_ref(x_84);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_53;
}
}
block_32:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_25 = lean_mk_string_unchecked("`<;>` failed", 12, 12);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(x_26, x_24, x_22, x_18, x_17, x_13);
lean_dec(x_17);
lean_dec(x_18);
lean_dec(x_22);
lean_dec(x_24);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lam__0), 12, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
x_14 = l_Lean_Elab_Tactic_focus(lean_box(0), x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__3(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_2, x_1);
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
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_uget(x_3, x_2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = lean_eval_suggest_tactic(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = lean_array_uset(x_3, x_2, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_usize_of_nat(x_22);
x_24 = lean_usize_add(x_2, x_23);
x_25 = lean_array_uset(x_21, x_2, x_18);
x_2 = x_24;
x_3 = x_25;
x_13 = x_19;
goto _start;
}
else
{
uint8_t x_27; 
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
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_nat_dec_lt(x_4, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_18 = lean_mk_string_unchecked("tactic", 6, 6);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_instInhabitedTSyntax(x_21);
lean_dec(x_21);
x_23 = lean_array_get(x_22, x_1, x_4);
x_24 = lean_ctor_get(x_5, 0);
x_25 = lean_box(0);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_inc(x_24);
x_27 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_unbox(x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_28);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_29 = lean_eval_suggest_tactic(x_23, x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq(x_3, x_30);
x_33 = lean_ctor_get(x_2, 2);
x_34 = lean_nat_add(x_4, x_33);
lean_dec(x_4);
x_3 = x_32;
x_4 = x_34;
x_14 = x_31;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_29);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__1___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__2___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_12 = lean_array_uget(x_5, x_4);
lean_inc(x_1);
x_13 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq(x_1, x_12);
x_14 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq(x_13, x_11, x_6, x_7, x_8);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_array_uset(x_5, x_4, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_add(x_4, x_20);
x_22 = lean_array_uset(x_18, x_4, x_15);
x_4 = x_21;
x_5 = x_22;
x_8 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_12 == 0)
{
size_t x_13; lean_object* x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_array_size(x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_usize_of_nat(x_14);
lean_inc(x_10);
lean_inc(x_9);
x_16 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__0(x_13, x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq(x_17, x_12, x_9, x_10, x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_17);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_mk_empty_array_with_capacity(x_24);
x_26 = lean_array_get_size(x_1);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_sub(x_26, x_27);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_27);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_30 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__1___redArg(x_1, x_29, x_25, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_mk_string_unchecked("tactic", 6, 6);
x_34 = l_Lean_Name_mkStr1(x_33);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_instInhabitedTSyntax(x_36);
lean_dec(x_36);
x_38 = l_Array_back_x21(lean_box(0), x_37, x_1);
lean_dec(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_39 = lean_eval_suggest_tactic(x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic(x_40);
x_43 = lean_array_size(x_42);
x_44 = lean_usize_of_nat(x_24);
x_45 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__2___redArg(x_31, x_2, x_43, x_44, x_42, x_9, x_10, x_41);
lean_dec(x_2);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg(x_46, x_7, x_8, x_9, x_10, x_47);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_46);
return x_48;
}
else
{
lean_dec(x_31);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_39;
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
x_49 = !lean_is_exclusive(x_30);
if (x_49 == 0)
{
return x_30;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_30, 0);
x_51 = lean_ctor_get(x_30, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_30);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_15 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_16 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__0(x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__2___redArg(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_18 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq_spec__2(x_1, x_2, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_box(0);
lean_inc(x_3);
x_6 = lean_array_uset(x_3, x_2, x_5);
x_7 = lean_array_uget(x_3, x_2);
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_6, x_2, x_7);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_size(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_usize_of_nat(x_13);
x_15 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore_spec__0(x_12, x_14, x_1);
x_16 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Parser", 6, 6);
x_14 = lean_mk_string_unchecked("Tactic", 6, 6);
x_15 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_16 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_15);
lean_inc(x_1);
x_17 = l_Lean_Syntax_isOfKind(x_1, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_mk_string_unchecked("unexpected sequence", 19, 19);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(x_19, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Syntax_getArg(x_1, x_25);
lean_dec(x_1);
x_27 = lean_mk_string_unchecked("tacticSeqBracketed", 18, 18);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_28 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_27);
lean_inc(x_26);
x_29 = l_Lean_Syntax_isOfKind(x_26, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
x_31 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_30);
lean_inc(x_26);
x_32 = l_Lean_Syntax_isOfKind(x_26, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_mk_string_unchecked("unexpected sequence", 19, 19);
x_34 = l_Lean_stringToMessageData(x_33);
lean_dec(x_33);
x_35 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(x_34, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = l_Lean_Syntax_getArg(x_26, x_25);
lean_dec(x_26);
x_41 = l_Lean_Syntax_getArgs(x_40);
lean_dec(x_40);
x_42 = l_Lean_Syntax_TSepArray_getElems___redArg(x_41);
lean_dec(x_41);
x_43 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_44 = lean_unsigned_to_nat(1u);
x_45 = l_Lean_Syntax_getArg(x_26, x_44);
lean_dec(x_26);
x_46 = l_Lean_Syntax_getArgs(x_45);
lean_dec(x_45);
x_47 = l_Lean_Syntax_TSepArray_getElems___redArg(x_46);
lean_dec(x_46);
x_48 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq(x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_13);
x_16 = lean_nat_dec_eq(x_2, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_mk_string_unchecked("Lean", 4, 4);
x_18 = lean_mk_string_unchecked("Parser", 6, 6);
x_19 = lean_mk_string_unchecked("Tactic", 6, 6);
x_20 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_21 = l_Lean_Name_mkStr4(x_17, x_18, x_19, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Elab_Tactic_saveState___redArg(x_5, x_7, x_9, x_10, x_11, x_12);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_instInhabitedTSyntax(x_23);
lean_dec(x_23);
x_28 = lean_array_get(x_27, x_1, x_2);
lean_inc(x_3);
x_29 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq), 11, 2);
lean_closure_set(x_29, 0, x_28);
lean_closure_set(x_29, 1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_30 = l_Lean_Elab_Tactic_withoutRecover(lean_box(0), x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_39; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
x_39 = l_Lean_Exception_isInterrupt(x_31);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Exception_isRuntime(x_31);
lean_dec(x_31);
x_33 = x_40;
goto block_38;
}
else
{
lean_dec(x_31);
x_33 = x_39;
goto block_38;
}
block_38:
{
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_30);
x_34 = l_Lean_Elab_Tactic_SavedState_restore(x_25, x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_2 = x_36;
x_12 = x_35;
goto _start;
}
else
{
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_30;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_mk_string_unchecked("Lean", 4, 4);
x_42 = lean_mk_string_unchecked("Parser", 6, 6);
x_43 = lean_mk_string_unchecked("Tactic", 6, 6);
x_44 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_45 = l_Lean_Name_mkStr4(x_41, x_42, x_43, x_44);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_instInhabitedTSyntax(x_47);
lean_dec(x_47);
x_49 = lean_array_get(x_48, x_1, x_2);
lean_dec(x_2);
x_50 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq(x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst_go(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_mk_string_unchecked("`first` expects at least one argument", 37, 37);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
x_18 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(x_17, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Elab_Tactic_saveState___redArg(x_4, x_6, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq), 11, 2);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Elab_Tactic_withoutRecover(lean_box(0), x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_60; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_60 = l_Lean_Exception_isInterrupt(x_17);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = l_Lean_Exception_isRuntime(x_17);
lean_dec(x_17);
x_19 = x_61;
goto block_59;
}
else
{
lean_dec(x_17);
x_19 = x_60;
goto block_59;
}
block_59:
{
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_16);
x_20 = l_Lean_Elab_Tactic_SavedState_restore(x_13, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 1);
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_st_ref_get(x_10, x_22);
lean_dec(x_10);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_9, 5);
lean_inc(x_27);
lean_dec(x_9);
x_28 = l_Lean_SourceInfo_fromRef(x_27, x_19);
lean_dec(x_27);
x_29 = lean_mk_string_unchecked("Lean", 4, 4);
x_30 = lean_mk_string_unchecked("Parser", 6, 6);
x_31 = lean_mk_string_unchecked("Tactic", 6, 6);
x_32 = lean_mk_string_unchecked("skip", 4, 4);
lean_inc(x_32);
x_33 = l_Lean_Name_mkStr4(x_29, x_30, x_31, x_32);
lean_inc(x_28);
lean_ctor_set_tag(x_20, 2);
lean_ctor_set(x_20, 1, x_32);
lean_ctor_set(x_20, 0, x_28);
x_34 = l_Lean_Syntax_node1(x_28, x_33, x_20);
lean_ctor_set(x_24, 0, x_34);
return x_24;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_dec(x_24);
x_36 = lean_ctor_get(x_9, 5);
lean_inc(x_36);
lean_dec(x_9);
x_37 = l_Lean_SourceInfo_fromRef(x_36, x_19);
lean_dec(x_36);
x_38 = lean_mk_string_unchecked("Lean", 4, 4);
x_39 = lean_mk_string_unchecked("Parser", 6, 6);
x_40 = lean_mk_string_unchecked("Tactic", 6, 6);
x_41 = lean_mk_string_unchecked("skip", 4, 4);
lean_inc(x_41);
x_42 = l_Lean_Name_mkStr4(x_38, x_39, x_40, x_41);
lean_inc(x_37);
lean_ctor_set_tag(x_20, 2);
lean_ctor_set(x_20, 1, x_41);
lean_ctor_set(x_20, 0, x_37);
x_43 = l_Lean_Syntax_node1(x_37, x_42, x_20);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_35);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_dec(x_20);
x_46 = lean_st_ref_get(x_10, x_45);
lean_dec(x_10);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_9, 5);
lean_inc(x_49);
lean_dec(x_9);
x_50 = l_Lean_SourceInfo_fromRef(x_49, x_19);
lean_dec(x_49);
x_51 = lean_mk_string_unchecked("Lean", 4, 4);
x_52 = lean_mk_string_unchecked("Parser", 6, 6);
x_53 = lean_mk_string_unchecked("Tactic", 6, 6);
x_54 = lean_mk_string_unchecked("skip", 4, 4);
lean_inc(x_54);
x_55 = l_Lean_Name_mkStr4(x_51, x_52, x_53, x_54);
lean_inc(x_50);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Syntax_node1(x_50, x_55, x_56);
if (lean_is_scalar(x_48)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_48;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_47);
return x_58;
}
}
else
{
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTry(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_1);
x_16 = lean_nat_dec_lt(x_2, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_17 = lean_mk_string_unchecked("`attempt_all` failed", 20, 20);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(x_18, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = l_Lean_Elab_Tactic_SavedState_restore(x_20, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___redArg(x_4, x_10, x_11, x_12, x_13, x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_mk_string_unchecked("Lean", 4, 4);
x_25 = lean_mk_string_unchecked("Parser", 6, 6);
x_26 = lean_mk_string_unchecked("Tactic", 6, 6);
x_27 = lean_mk_string_unchecked("tacticSeq", 9, 9);
x_28 = l_Lean_Name_mkStr4(x_24, x_25, x_26, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_instInhabitedTSyntax(x_30);
lean_dec(x_30);
x_32 = lean_array_get(x_31, x_1, x_2);
x_33 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq), 11, 1);
lean_closure_set(x_33, 0, x_32);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_34 = l_Lean_Elab_Tactic_Try_observing___redArg(x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
x_69 = lean_mk_string_unchecked("try", 3, 3);
x_70 = lean_mk_string_unchecked("debug", 5, 5);
x_71 = l_Lean_Name_mkStr2(x_69, x_70);
lean_inc(x_71);
x_72 = l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg(x_71, x_12, x_36);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_71);
lean_free_object(x_35);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_55 = x_5;
x_56 = x_6;
x_57 = x_7;
x_58 = x_8;
x_59 = x_9;
x_60 = x_10;
x_61 = x_11;
x_62 = x_12;
x_63 = x_13;
x_64 = x_75;
goto block_68;
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_72);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_72, 1);
x_78 = lean_ctor_get(x_72, 0);
lean_dec(x_78);
x_79 = lean_mk_string_unchecked("`attempt_all` argument succeeded", 32, 32);
x_80 = l_Lean_stringToMessageData(x_79);
lean_dec(x_79);
lean_inc(x_38);
x_81 = l_Lean_MessageData_ofSyntax(x_38);
x_82 = l_Lean_indentD(x_81);
lean_ctor_set_tag(x_72, 7);
lean_ctor_set(x_72, 1, x_82);
lean_ctor_set(x_72, 0, x_80);
x_83 = lean_mk_string_unchecked("", 0, 0);
x_84 = l_Lean_stringToMessageData(x_83);
lean_dec(x_83);
lean_ctor_set_tag(x_35, 7);
lean_ctor_set(x_35, 1, x_84);
lean_ctor_set(x_35, 0, x_72);
x_85 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_71, x_35, x_10, x_11, x_12, x_13, x_77);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_55 = x_5;
x_56 = x_6;
x_57 = x_7;
x_58 = x_8;
x_59 = x_9;
x_60 = x_10;
x_61 = x_11;
x_62 = x_12;
x_63 = x_13;
x_64 = x_86;
goto block_68;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_87 = lean_ctor_get(x_72, 1);
lean_inc(x_87);
lean_dec(x_72);
x_88 = lean_mk_string_unchecked("`attempt_all` argument succeeded", 32, 32);
x_89 = l_Lean_stringToMessageData(x_88);
lean_dec(x_88);
lean_inc(x_38);
x_90 = l_Lean_MessageData_ofSyntax(x_38);
x_91 = l_Lean_indentD(x_90);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_mk_string_unchecked("", 0, 0);
x_94 = l_Lean_stringToMessageData(x_93);
lean_dec(x_93);
lean_ctor_set_tag(x_35, 7);
lean_ctor_set(x_35, 1, x_94);
lean_ctor_set(x_35, 0, x_92);
x_95 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_71, x_35, x_10, x_11, x_12, x_13, x_87);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_55 = x_5;
x_56 = x_6;
x_57 = x_7;
x_58 = x_8;
x_59 = x_9;
x_60 = x_10;
x_61 = x_11;
x_62 = x_12;
x_63 = x_13;
x_64 = x_96;
goto block_68;
}
}
block_54:
{
lean_object* x_52; 
x_52 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSuggestion(x_4, x_38);
x_2 = x_45;
x_3 = x_51;
x_4 = x_52;
x_5 = x_50;
x_6 = x_49;
x_7 = x_48;
x_8 = x_44;
x_9 = x_43;
x_10 = x_42;
x_11 = x_46;
x_12 = x_41;
x_13 = x_47;
x_14 = x_40;
goto _start;
}
block_68:
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_2, x_65);
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_39);
x_40 = x_64;
x_41 = x_62;
x_42 = x_60;
x_43 = x_59;
x_44 = x_58;
x_45 = x_66;
x_46 = x_61;
x_47 = x_63;
x_48 = x_57;
x_49 = x_56;
x_50 = x_55;
x_51 = x_67;
goto block_54;
}
else
{
lean_dec(x_39);
x_40 = x_64;
x_41 = x_62;
x_42 = x_60;
x_43 = x_59;
x_44 = x_58;
x_45 = x_66;
x_46 = x_61;
x_47 = x_63;
x_48 = x_57;
x_49 = x_56;
x_50 = x_55;
x_51 = x_3;
goto block_54;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_97 = lean_ctor_get(x_35, 0);
x_98 = lean_ctor_get(x_35, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_35);
x_128 = lean_mk_string_unchecked("try", 3, 3);
x_129 = lean_mk_string_unchecked("debug", 5, 5);
x_130 = l_Lean_Name_mkStr2(x_128, x_129);
lean_inc(x_130);
x_131 = l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg(x_130, x_12, x_36);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec(x_130);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_114 = x_5;
x_115 = x_6;
x_116 = x_7;
x_117 = x_8;
x_118 = x_9;
x_119 = x_10;
x_120 = x_11;
x_121 = x_12;
x_122 = x_13;
x_123 = x_134;
goto block_127;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_135 = lean_ctor_get(x_131, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_136 = x_131;
} else {
 lean_dec_ref(x_131);
 x_136 = lean_box(0);
}
x_137 = lean_mk_string_unchecked("`attempt_all` argument succeeded", 32, 32);
x_138 = l_Lean_stringToMessageData(x_137);
lean_dec(x_137);
lean_inc(x_97);
x_139 = l_Lean_MessageData_ofSyntax(x_97);
x_140 = l_Lean_indentD(x_139);
if (lean_is_scalar(x_136)) {
 x_141 = lean_alloc_ctor(7, 2, 0);
} else {
 x_141 = x_136;
 lean_ctor_set_tag(x_141, 7);
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_mk_string_unchecked("", 0, 0);
x_143 = l_Lean_stringToMessageData(x_142);
lean_dec(x_142);
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_143);
x_145 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_130, x_144, x_10, x_11, x_12, x_13, x_135);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_114 = x_5;
x_115 = x_6;
x_116 = x_7;
x_117 = x_8;
x_118 = x_9;
x_119 = x_10;
x_120 = x_11;
x_121 = x_12;
x_122 = x_13;
x_123 = x_146;
goto block_127;
}
block_113:
{
lean_object* x_111; 
x_111 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSuggestion(x_4, x_97);
x_2 = x_104;
x_3 = x_110;
x_4 = x_111;
x_5 = x_109;
x_6 = x_108;
x_7 = x_107;
x_8 = x_103;
x_9 = x_102;
x_10 = x_101;
x_11 = x_105;
x_12 = x_100;
x_13 = x_106;
x_14 = x_99;
goto _start;
}
block_127:
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_unsigned_to_nat(1u);
x_125 = lean_nat_add(x_2, x_124);
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_98);
x_99 = x_123;
x_100 = x_121;
x_101 = x_119;
x_102 = x_118;
x_103 = x_117;
x_104 = x_125;
x_105 = x_120;
x_106 = x_122;
x_107 = x_116;
x_108 = x_115;
x_109 = x_114;
x_110 = x_126;
goto block_113;
}
else
{
lean_dec(x_98);
x_99 = x_123;
x_100 = x_121;
x_101 = x_119;
x_102 = x_118;
x_103 = x_117;
x_104 = x_125;
x_105 = x_120;
x_106 = x_122;
x_107 = x_116;
x_108 = x_115;
x_109 = x_114;
x_110 = x_3;
goto block_113;
}
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_35);
x_147 = lean_ctor_get(x_34, 1);
lean_inc(x_147);
lean_dec(x_34);
x_148 = lean_unsigned_to_nat(1u);
x_149 = lean_nat_add(x_2, x_148);
lean_dec(x_2);
x_2 = x_149;
x_14 = x_147;
goto _start;
}
}
else
{
uint8_t x_151; 
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
lean_dec(x_2);
x_151 = !lean_is_exclusive(x_34);
if (x_151 == 0)
{
return x_34;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_34, 0);
x_153 = lean_ctor_get(x_34, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_34);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_mk_string_unchecked("invalid occurrence of `attempt_all` in non-terminal position for `try\?` script", 78, 78);
x_14 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_Lean_MessageData_ofSyntax(x_15);
x_17 = l_Lean_indentD(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_string_unchecked("", 0, 0);
x_20 = l_Lean_stringToMessageData(x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(x_21, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_box(0);
x_29 = lean_mk_empty_array_with_capacity(x_27);
x_30 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go(x_1, x_27, x_28, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_throwExs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_replaceRef(x_1, x_8);
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_5, 2);
x_13 = lean_ctor_get(x_5, 3);
x_14 = lean_ctor_get(x_5, 4);
x_15 = lean_ctor_get(x_5, 6);
x_16 = lean_ctor_get(x_5, 7);
x_17 = lean_ctor_get(x_5, 8);
x_18 = lean_ctor_get(x_5, 9);
x_19 = lean_ctor_get(x_5, 10);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*13);
x_21 = lean_ctor_get(x_5, 11);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_23 = lean_ctor_get(x_5, 12);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_24 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_11);
lean_ctor_set(x_24, 2, x_12);
lean_ctor_set(x_24, 3, x_13);
lean_ctor_set(x_24, 4, x_14);
lean_ctor_set(x_24, 5, x_9);
lean_ctor_set(x_24, 6, x_15);
lean_ctor_set(x_24, 7, x_16);
lean_ctor_set(x_24, 8, x_17);
lean_ctor_set(x_24, 9, x_18);
lean_ctor_set(x_24, 10, x_19);
lean_ctor_set(x_24, 11, x_21);
lean_ctor_set(x_24, 12, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*13, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*13 + 1, x_22);
x_25 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(x_2, x_3, x_4, x_24, x_6, x_7);
lean_dec(x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_throwExs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_throwErrorAt___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_throwExs_spec__0___redArg(x_2, x_3, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_throwExs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_2);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
x_16 = lean_mk_string_unchecked("unexpected syntax ", 18, 18);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
lean_inc(x_1);
x_18 = l_Lean_MessageData_ofSyntax(x_1);
x_19 = l_Lean_indentD(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked("", 0, 0);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwErrorAt___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_throwExs_spec__0___redArg(x_1, x_23, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_1);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_14, x_25);
lean_dec(x_14);
x_27 = lean_array_fget(x_2, x_26);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = l_Lean_Elab_Tactic_SavedState_restore(x_28, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
lean_dec(x_27);
lean_ctor_set_tag(x_29, 1);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_throwExs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwErrorAt___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_throwExs_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_throwExs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_throwErrorAt___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_throwExs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_throwExs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_throwExs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_eval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_throwExs(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_1);
x_23 = lean_apply_11(x_18, x_1, x_5, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_67; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
x_67 = l_Lean_Exception_isInterrupt(x_24);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = l_Lean_Exception_isRuntime(x_24);
x_26 = x_68;
goto block_66;
}
else
{
x_26 = x_67;
goto block_66;
}
block_66:
{
if (x_26 == 0)
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_23);
x_27 = l_Lean_Elab_Tactic_saveState___redArg(x_7, x_9, x_11, x_12, x_13, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(1);
x_31 = lean_unbox(x_30);
lean_inc(x_2);
x_32 = l_Lean_Elab_Tactic_SavedState_restore(x_2, x_31, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_29);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 1);
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 0, x_24);
x_36 = lean_array_push(x_4, x_32);
x_3 = x_17;
x_4 = x_36;
x_14 = x_34;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_28);
x_40 = lean_array_push(x_4, x_39);
x_3 = x_17;
x_4 = x_40;
x_14 = x_38;
goto _start;
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_24, 0);
lean_inc(x_42);
x_43 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_44 = l___private_Lean_InternalExceptionId_0__Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_26_(x_42, x_43);
x_45 = lean_box(1);
if (x_44 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = l_Lean_Elab_abortTacticExceptionId;
x_47 = l___private_Lean_InternalExceptionId_0__Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_26_(x_42, x_46);
lean_dec(x_42);
if (x_47 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_23;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_23);
x_48 = l_Lean_Elab_Tactic_saveState___redArg(x_7, x_9, x_11, x_12, x_13, x_25);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_unbox(x_45);
lean_inc(x_2);
x_52 = l_Lean_Elab_Tactic_SavedState_restore(x_2, x_51, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_50);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 1);
x_55 = lean_ctor_get(x_52, 0);
lean_dec(x_55);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 0, x_24);
x_56 = lean_array_push(x_4, x_52);
x_3 = x_17;
x_4 = x_56;
x_14 = x_54;
goto _start;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_dec(x_52);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_24);
lean_ctor_set(x_59, 1, x_49);
x_60 = lean_array_push(x_4, x_59);
x_3 = x_17;
x_4 = x_60;
x_14 = x_58;
goto _start;
}
}
}
else
{
uint8_t x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_42);
lean_dec(x_24);
lean_dec(x_23);
x_62 = lean_unbox(x_45);
lean_inc(x_2);
x_63 = l_Lean_Elab_Tactic_SavedState_restore(x_2, x_62, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_25);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_3 = x_17;
x_14 = x_64;
goto _start;
}
}
}
else
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_23;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_eval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_eval(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = l_Lean_Syntax_getKind(x_1);
x_13 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getEvalFns___redArg(x_12, x_10, x_11);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l_Lean_Elab_Tactic_saveState___redArg(x_4, x_6, x_8, x_9, x_10, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_mk_empty_array_with_capacity(x_21);
x_23 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault_eval(x_1, x_19, x_14, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
lean_dec(x_3);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_mk_string_unchecked("group", 5, 5);
x_8 = l_Lean_Name_mkStr1(x_7);
lean_inc(x_6);
x_9 = l_Lean_Syntax_isOfKind(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_3);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_box(0);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_array_uset(x_3, x_2, x_11);
x_14 = l_Lean_Syntax_getArg(x_6, x_12);
lean_dec(x_6);
x_15 = lean_usize_of_nat(x_12);
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_13, x_2, x_14);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lean_eval_suggest_tactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; 
x_404 = lean_mk_string_unchecked("try", 3, 3);
x_405 = lean_mk_string_unchecked("debug", 5, 5);
x_406 = l_Lean_Name_mkStr2(x_404, x_405);
lean_inc(x_406);
x_407 = l_Lean_isTracingEnabledFor___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__0___redArg(x_406, x_9, x_11);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_unbox(x_408);
lean_dec(x_408);
if (x_409 == 0)
{
lean_object* x_410; 
lean_dec(x_406);
x_410 = lean_ctor_get(x_407, 1);
lean_inc(x_410);
lean_dec(x_407);
x_197 = x_2;
x_198 = x_3;
x_199 = x_4;
x_200 = x_5;
x_201 = x_6;
x_202 = x_7;
x_203 = x_8;
x_204 = x_9;
x_205 = x_10;
x_206 = x_410;
goto block_403;
}
else
{
uint8_t x_411; 
x_411 = !lean_is_exclusive(x_407);
if (x_411 == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_412 = lean_ctor_get(x_407, 1);
x_413 = lean_ctor_get(x_407, 0);
lean_dec(x_413);
x_414 = lean_mk_string_unchecked("", 0, 0);
x_415 = l_Lean_stringToMessageData(x_414);
lean_dec(x_414);
lean_inc(x_1);
x_416 = l_Lean_MessageData_ofSyntax(x_1);
lean_inc(x_415);
lean_ctor_set_tag(x_407, 7);
lean_ctor_set(x_407, 1, x_416);
lean_ctor_set(x_407, 0, x_415);
x_417 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_417, 0, x_407);
lean_ctor_set(x_417, 1, x_415);
x_418 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_406, x_417, x_7, x_8, x_9, x_10, x_412);
x_419 = lean_ctor_get(x_418, 1);
lean_inc(x_419);
lean_dec(x_418);
x_197 = x_2;
x_198 = x_3;
x_199 = x_4;
x_200 = x_5;
x_201 = x_6;
x_202 = x_7;
x_203 = x_8;
x_204 = x_9;
x_205 = x_10;
x_206 = x_419;
goto block_403;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_420 = lean_ctor_get(x_407, 1);
lean_inc(x_420);
lean_dec(x_407);
x_421 = lean_mk_string_unchecked("", 0, 0);
x_422 = l_Lean_stringToMessageData(x_421);
lean_dec(x_421);
lean_inc(x_1);
x_423 = l_Lean_MessageData_ofSyntax(x_1);
lean_inc(x_422);
x_424 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_423);
x_425 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_422);
x_426 = l_Lean_addTrace___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_spec__9___redArg(x_406, x_425, x_7, x_8, x_9, x_10, x_420);
x_427 = lean_ctor_get(x_426, 1);
lean_inc(x_427);
lean_dec(x_426);
x_197 = x_2;
x_198 = x_3;
x_199 = x_4;
x_200 = x_5;
x_201 = x_6;
x_202 = x_7;
x_203 = x_8;
x_204 = x_9;
x_205 = x_10;
x_206 = x_427;
goto block_403;
}
}
block_48:
{
uint8_t x_23; 
x_23 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec(x_13);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Elab_Tactic_getGoals(x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = l_List_isEmpty___redArg(x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_free_object(x_25);
lean_dec(x_12);
x_30 = lean_mk_string_unchecked("unsolved goals", 14, 14);
x_31 = l_Lean_stringToMessageData(x_30);
lean_dec(x_30);
x_32 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(x_31, x_18, x_19, x_20, x_21, x_28);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_ctor_set(x_25, 0, x_12);
return x_25;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_25, 0);
x_38 = lean_ctor_get(x_25, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_25);
x_39 = l_List_isEmpty___redArg(x_37);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_12);
x_40 = lean_mk_string_unchecked("unsolved goals", 14, 14);
x_41 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
x_42 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(x_41, x_18, x_19, x_20, x_21, x_38);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
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
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
else
{
lean_object* x_47; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_12);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
}
}
block_85:
{
uint8_t x_60; 
x_60 = lean_ctor_get_uint8(x_50, sizeof(void*)*2);
lean_dec(x_50);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_49);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
else
{
lean_object* x_62; uint8_t x_63; 
x_62 = l_Lean_Elab_Tactic_getGoals(x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_59);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
x_66 = l_List_isEmpty___redArg(x_64);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_free_object(x_62);
lean_dec(x_49);
x_67 = lean_mk_string_unchecked("unsolved goals", 14, 14);
x_68 = l_Lean_stringToMessageData(x_67);
lean_dec(x_67);
x_69 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(x_68, x_55, x_56, x_57, x_58, x_65);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
return x_69;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_69);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
else
{
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_ctor_set(x_62, 0, x_49);
return x_62;
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_62, 0);
x_75 = lean_ctor_get(x_62, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_62);
x_76 = l_List_isEmpty___redArg(x_74);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_49);
x_77 = lean_mk_string_unchecked("unsolved goals", 14, 14);
x_78 = l_Lean_stringToMessageData(x_77);
lean_dec(x_77);
x_79 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(x_78, x_55, x_56, x_57, x_58, x_75);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
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
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
else
{
lean_object* x_84; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_49);
lean_ctor_set(x_84, 1, x_75);
return x_84;
}
}
}
}
block_122:
{
uint8_t x_97; 
x_97 = lean_ctor_get_uint8(x_87, sizeof(void*)*2);
lean_dec(x_87);
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_86);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
else
{
lean_object* x_99; uint8_t x_100; 
x_99 = l_Lean_Elab_Tactic_getGoals(x_88, x_89, x_90, x_91, x_92, x_93, x_94, x_95, x_96);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_ctor_get(x_99, 1);
x_103 = l_List_isEmpty___redArg(x_101);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_free_object(x_99);
lean_dec(x_86);
x_104 = lean_mk_string_unchecked("unsolved goals", 14, 14);
x_105 = l_Lean_stringToMessageData(x_104);
lean_dec(x_104);
x_106 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(x_105, x_92, x_93, x_94, x_95, x_102);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
return x_106;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_106, 0);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_106);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
else
{
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_ctor_set(x_99, 0, x_86);
return x_99;
}
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_99, 0);
x_112 = lean_ctor_get(x_99, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_99);
x_113 = l_List_isEmpty___redArg(x_111);
lean_dec(x_111);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_86);
x_114 = lean_mk_string_unchecked("unsolved goals", 14, 14);
x_115 = l_Lean_stringToMessageData(x_114);
lean_dec(x_114);
x_116 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(x_115, x_92, x_93, x_94, x_95, x_112);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
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
else
{
lean_object* x_121; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_86);
lean_ctor_set(x_121, 1, x_112);
return x_121;
}
}
}
}
block_159:
{
uint8_t x_134; 
x_134 = lean_ctor_get_uint8(x_124, sizeof(void*)*2);
lean_dec(x_124);
if (x_134 == 0)
{
lean_object* x_135; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_123);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
else
{
lean_object* x_136; uint8_t x_137; 
x_136 = l_Lean_Elab_Tactic_getGoals(x_125, x_126, x_127, x_128, x_129, x_130, x_131, x_132, x_133);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_138 = lean_ctor_get(x_136, 0);
x_139 = lean_ctor_get(x_136, 1);
x_140 = l_List_isEmpty___redArg(x_138);
lean_dec(x_138);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_free_object(x_136);
lean_dec(x_123);
x_141 = lean_mk_string_unchecked("unsolved goals", 14, 14);
x_142 = l_Lean_stringToMessageData(x_141);
lean_dec(x_141);
x_143 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(x_142, x_129, x_130, x_131, x_132, x_139);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
return x_143;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_143, 0);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_143);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
else
{
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_ctor_set(x_136, 0, x_123);
return x_136;
}
}
else
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_148 = lean_ctor_get(x_136, 0);
x_149 = lean_ctor_get(x_136, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_136);
x_150 = l_List_isEmpty___redArg(x_148);
lean_dec(x_148);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_123);
x_151 = lean_mk_string_unchecked("unsolved goals", 14, 14);
x_152 = l_Lean_stringToMessageData(x_151);
lean_dec(x_151);
x_153 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(x_152, x_129, x_130, x_131, x_132, x_149);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
else
{
lean_object* x_158; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_123);
lean_ctor_set(x_158, 1, x_149);
return x_158;
}
}
}
}
block_196:
{
uint8_t x_171; 
x_171 = lean_ctor_get_uint8(x_161, sizeof(void*)*2);
lean_dec(x_161);
if (x_171 == 0)
{
lean_object* x_172; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_160);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
else
{
lean_object* x_173; uint8_t x_174; 
x_173 = l_Lean_Elab_Tactic_getGoals(x_162, x_163, x_164, x_165, x_166, x_167, x_168, x_169, x_170);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_175 = lean_ctor_get(x_173, 0);
x_176 = lean_ctor_get(x_173, 1);
x_177 = l_List_isEmpty___redArg(x_175);
lean_dec(x_175);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
lean_free_object(x_173);
lean_dec(x_160);
x_178 = lean_mk_string_unchecked("unsolved goals", 14, 14);
x_179 = l_Lean_stringToMessageData(x_178);
lean_dec(x_178);
x_180 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(x_179, x_166, x_167, x_168, x_169, x_176);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
x_181 = !lean_is_exclusive(x_180);
if (x_181 == 0)
{
return x_180;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_180, 0);
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_180);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
else
{
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_ctor_set(x_173, 0, x_160);
return x_173;
}
}
else
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_185 = lean_ctor_get(x_173, 0);
x_186 = lean_ctor_get(x_173, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_173);
x_187 = l_List_isEmpty___redArg(x_185);
lean_dec(x_185);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_160);
x_188 = lean_mk_string_unchecked("unsolved goals", 14, 14);
x_189 = l_Lean_stringToMessageData(x_188);
lean_dec(x_188);
x_190 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain_spec__2___redArg(x_189, x_166, x_167, x_168, x_169, x_186);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_193 = x_190;
} else {
 lean_dec_ref(x_190);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
else
{
lean_object* x_195; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_160);
lean_ctor_set(x_195, 1, x_186);
return x_195;
}
}
}
}
block_403:
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_207 = lean_mk_string_unchecked("Lean", 4, 4);
x_208 = lean_mk_string_unchecked("Parser", 6, 6);
x_209 = lean_mk_string_unchecked("Tactic", 6, 6);
x_210 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_211 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_210);
lean_inc(x_1);
x_212 = l_Lean_Syntax_isOfKind(x_1, x_211);
lean_dec(x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_213 = lean_mk_string_unchecked("first", 5, 5);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_214 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_213);
lean_inc(x_1);
x_215 = l_Lean_Syntax_isOfKind(x_1, x_214);
lean_dec(x_214);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_216 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_217 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_216);
lean_inc(x_1);
x_218 = l_Lean_Syntax_isOfKind(x_1, x_217);
lean_dec(x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_219 = lean_mk_string_unchecked("tacticTry_", 10, 10);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_220 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_219);
lean_inc(x_1);
x_221 = l_Lean_Syntax_isOfKind(x_1, x_220);
lean_dec(x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_222 = lean_mk_string_unchecked("attemptAll", 10, 10);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_223 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_222);
lean_inc(x_1);
x_224 = l_Lean_Syntax_isOfKind(x_1, x_223);
lean_dec(x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
lean_inc(x_1);
x_225 = l_Lean_Syntax_getKind(x_1);
x_226 = lean_mk_string_unchecked("seq1", 4, 4);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_227 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_226);
x_228 = lean_name_eq(x_225, x_227);
lean_dec(x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_229 = lean_mk_string_unchecked("grindTrace", 10, 10);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_230 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_229);
x_231 = lean_name_eq(x_225, x_230);
lean_dec(x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_232 = lean_mk_string_unchecked("simpTrace", 9, 9);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_233 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_232);
x_234 = lean_name_eq(x_225, x_233);
lean_dec(x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; uint8_t x_237; 
x_235 = lean_mk_string_unchecked("exact\?", 6, 6);
x_236 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_235);
x_237 = lean_name_eq(x_225, x_236);
lean_dec(x_236);
lean_dec(x_225);
if (x_237 == 0)
{
lean_object* x_238; 
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
x_238 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault(x_1, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_49 = x_239;
x_50 = x_197;
x_51 = x_198;
x_52 = x_199;
x_53 = x_200;
x_54 = x_201;
x_55 = x_202;
x_56 = x_203;
x_57 = x_204;
x_58 = x_205;
x_59 = x_240;
goto block_85;
}
else
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
return x_238;
}
}
else
{
lean_object* x_241; 
lean_dec(x_1);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
x_241 = l_Lean_Elab_Tactic_Try_evalSuggestExact(x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_49 = x_242;
x_50 = x_197;
x_51 = x_198;
x_52 = x_199;
x_53 = x_200;
x_54 = x_201;
x_55 = x_202;
x_56 = x_203;
x_57 = x_204;
x_58 = x_205;
x_59 = x_243;
goto block_85;
}
else
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
return x_241;
}
}
}
else
{
lean_object* x_244; 
lean_dec(x_225);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
x_244 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace(x_1, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_49 = x_245;
x_50 = x_197;
x_51 = x_198;
x_52 = x_199;
x_53 = x_200;
x_54 = x_201;
x_55 = x_202;
x_56 = x_203;
x_57 = x_204;
x_58 = x_205;
x_59 = x_246;
goto block_85;
}
else
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
return x_244;
}
}
}
else
{
lean_object* x_247; 
lean_dec(x_225);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
x_247 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace(x_1, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_49 = x_248;
x_50 = x_197;
x_51 = x_198;
x_52 = x_199;
x_53 = x_200;
x_54 = x_201;
x_55 = x_202;
x_56 = x_203;
x_57 = x_204;
x_58 = x_205;
x_59 = x_249;
goto block_85;
}
else
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
return x_247;
}
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_225);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
x_250 = lean_unsigned_to_nat(0u);
x_251 = l_Lean_Syntax_getArg(x_1, x_250);
lean_dec(x_1);
x_252 = l_Lean_Syntax_getSepArgs(x_251);
lean_dec(x_251);
x_253 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore(x_252, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
return x_253;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; size_t x_257; lean_object* x_258; size_t x_259; lean_object* x_260; 
x_254 = lean_unsigned_to_nat(1u);
x_255 = l_Lean_Syntax_getArg(x_1, x_254);
x_256 = l_Lean_Syntax_getArgs(x_255);
lean_dec(x_255);
x_257 = lean_array_size(x_256);
x_258 = lean_unsigned_to_nat(0u);
x_259 = lean_usize_of_nat(x_258);
x_260 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl_spec__0(x_257, x_259, x_256);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; 
lean_inc(x_1);
x_261 = l_Lean_Syntax_getKind(x_1);
x_262 = lean_mk_string_unchecked("seq1", 4, 4);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_263 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_262);
x_264 = lean_name_eq(x_261, x_263);
lean_dec(x_263);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; uint8_t x_267; 
x_265 = lean_mk_string_unchecked("grindTrace", 10, 10);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_266 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_265);
x_267 = lean_name_eq(x_261, x_266);
lean_dec(x_266);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_268 = lean_mk_string_unchecked("simpTrace", 9, 9);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_269 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_268);
x_270 = lean_name_eq(x_261, x_269);
lean_dec(x_269);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; 
x_271 = lean_mk_string_unchecked("exact\?", 6, 6);
x_272 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_271);
x_273 = lean_name_eq(x_261, x_272);
lean_dec(x_272);
lean_dec(x_261);
if (x_273 == 0)
{
lean_object* x_274; 
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
x_274 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault(x_1, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
x_12 = x_275;
x_13 = x_197;
x_14 = x_198;
x_15 = x_199;
x_16 = x_200;
x_17 = x_201;
x_18 = x_202;
x_19 = x_203;
x_20 = x_204;
x_21 = x_205;
x_22 = x_276;
goto block_48;
}
else
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
return x_274;
}
}
else
{
lean_object* x_277; 
lean_dec(x_1);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
x_277 = l_Lean_Elab_Tactic_Try_evalSuggestExact(x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
x_12 = x_278;
x_13 = x_197;
x_14 = x_198;
x_15 = x_199;
x_16 = x_200;
x_17 = x_201;
x_18 = x_202;
x_19 = x_203;
x_20 = x_204;
x_21 = x_205;
x_22 = x_279;
goto block_48;
}
else
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
return x_277;
}
}
}
else
{
lean_object* x_280; 
lean_dec(x_261);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
x_280 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace(x_1, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
x_12 = x_281;
x_13 = x_197;
x_14 = x_198;
x_15 = x_199;
x_16 = x_200;
x_17 = x_201;
x_18 = x_202;
x_19 = x_203;
x_20 = x_204;
x_21 = x_205;
x_22 = x_282;
goto block_48;
}
else
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
return x_280;
}
}
}
else
{
lean_object* x_283; 
lean_dec(x_261);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
x_283 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace(x_1, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
x_12 = x_284;
x_13 = x_197;
x_14 = x_198;
x_15 = x_199;
x_16 = x_200;
x_17 = x_201;
x_18 = x_202;
x_19 = x_203;
x_20 = x_204;
x_21 = x_205;
x_22 = x_285;
goto block_48;
}
else
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
return x_283;
}
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_261);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
x_286 = l_Lean_Syntax_getArg(x_1, x_258);
lean_dec(x_1);
x_287 = l_Lean_Syntax_getSepArgs(x_286);
lean_dec(x_286);
x_288 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore(x_287, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
return x_288;
}
}
else
{
lean_object* x_289; lean_object* x_290; 
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_1);
x_289 = lean_ctor_get(x_260, 0);
lean_inc(x_289);
lean_dec(x_260);
x_290 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll(x_289, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
lean_dec(x_289);
return x_290;
}
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_291 = lean_unsigned_to_nat(1u);
x_292 = l_Lean_Syntax_getArg(x_1, x_291);
x_293 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_294 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_293);
lean_inc(x_292);
x_295 = l_Lean_Syntax_isOfKind(x_292, x_294);
lean_dec(x_294);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
lean_dec(x_292);
lean_inc(x_1);
x_296 = l_Lean_Syntax_getKind(x_1);
x_297 = lean_mk_string_unchecked("seq1", 4, 4);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_298 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_297);
x_299 = lean_name_eq(x_296, x_298);
lean_dec(x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_300 = lean_mk_string_unchecked("grindTrace", 10, 10);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_301 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_300);
x_302 = lean_name_eq(x_296, x_301);
lean_dec(x_301);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_303 = lean_mk_string_unchecked("simpTrace", 9, 9);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_304 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_303);
x_305 = lean_name_eq(x_296, x_304);
lean_dec(x_304);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_306 = lean_mk_string_unchecked("exact\?", 6, 6);
x_307 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_306);
x_308 = lean_name_eq(x_296, x_307);
lean_dec(x_307);
lean_dec(x_296);
if (x_308 == 0)
{
lean_object* x_309; 
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
x_309 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault(x_1, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
lean_dec(x_309);
x_86 = x_310;
x_87 = x_197;
x_88 = x_198;
x_89 = x_199;
x_90 = x_200;
x_91 = x_201;
x_92 = x_202;
x_93 = x_203;
x_94 = x_204;
x_95 = x_205;
x_96 = x_311;
goto block_122;
}
else
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
return x_309;
}
}
else
{
lean_object* x_312; 
lean_dec(x_1);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
x_312 = l_Lean_Elab_Tactic_Try_evalSuggestExact(x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
lean_dec(x_312);
x_86 = x_313;
x_87 = x_197;
x_88 = x_198;
x_89 = x_199;
x_90 = x_200;
x_91 = x_201;
x_92 = x_202;
x_93 = x_203;
x_94 = x_204;
x_95 = x_205;
x_96 = x_314;
goto block_122;
}
else
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
return x_312;
}
}
}
else
{
lean_object* x_315; 
lean_dec(x_296);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
x_315 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace(x_1, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_86 = x_316;
x_87 = x_197;
x_88 = x_198;
x_89 = x_199;
x_90 = x_200;
x_91 = x_201;
x_92 = x_202;
x_93 = x_203;
x_94 = x_204;
x_95 = x_205;
x_96 = x_317;
goto block_122;
}
else
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
return x_315;
}
}
}
else
{
lean_object* x_318; 
lean_dec(x_296);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
x_318 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace(x_1, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
x_86 = x_319;
x_87 = x_197;
x_88 = x_198;
x_89 = x_199;
x_90 = x_200;
x_91 = x_201;
x_92 = x_202;
x_93 = x_203;
x_94 = x_204;
x_95 = x_205;
x_96 = x_320;
goto block_122;
}
else
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
return x_318;
}
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_296);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
x_321 = lean_unsigned_to_nat(0u);
x_322 = l_Lean_Syntax_getArg(x_1, x_321);
lean_dec(x_1);
x_323 = l_Lean_Syntax_getSepArgs(x_322);
lean_dec(x_322);
x_324 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore(x_323, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
return x_324;
}
}
else
{
lean_object* x_325; 
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_1);
x_325 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTry(x_292, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
lean_dec(x_198);
return x_325;
}
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_326 = lean_unsigned_to_nat(1u);
x_327 = l_Lean_Syntax_getArg(x_1, x_326);
x_328 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_329 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_328);
lean_inc(x_327);
x_330 = l_Lean_Syntax_isOfKind(x_327, x_329);
lean_dec(x_329);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; 
lean_dec(x_327);
lean_inc(x_1);
x_331 = l_Lean_Syntax_getKind(x_1);
x_332 = lean_mk_string_unchecked("seq1", 4, 4);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_333 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_332);
x_334 = lean_name_eq(x_331, x_333);
lean_dec(x_333);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_335 = lean_mk_string_unchecked("grindTrace", 10, 10);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_336 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_335);
x_337 = lean_name_eq(x_331, x_336);
lean_dec(x_336);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_338 = lean_mk_string_unchecked("simpTrace", 9, 9);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_339 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_338);
x_340 = lean_name_eq(x_331, x_339);
lean_dec(x_339);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; uint8_t x_343; 
x_341 = lean_mk_string_unchecked("exact\?", 6, 6);
x_342 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_341);
x_343 = lean_name_eq(x_331, x_342);
lean_dec(x_342);
lean_dec(x_331);
if (x_343 == 0)
{
lean_object* x_344; 
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
x_344 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault(x_1, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; 
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
lean_dec(x_344);
x_123 = x_345;
x_124 = x_197;
x_125 = x_198;
x_126 = x_199;
x_127 = x_200;
x_128 = x_201;
x_129 = x_202;
x_130 = x_203;
x_131 = x_204;
x_132 = x_205;
x_133 = x_346;
goto block_159;
}
else
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
return x_344;
}
}
else
{
lean_object* x_347; 
lean_dec(x_1);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
x_347 = l_Lean_Elab_Tactic_Try_evalSuggestExact(x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; 
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_347, 1);
lean_inc(x_349);
lean_dec(x_347);
x_123 = x_348;
x_124 = x_197;
x_125 = x_198;
x_126 = x_199;
x_127 = x_200;
x_128 = x_201;
x_129 = x_202;
x_130 = x_203;
x_131 = x_204;
x_132 = x_205;
x_133 = x_349;
goto block_159;
}
else
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
return x_347;
}
}
}
else
{
lean_object* x_350; 
lean_dec(x_331);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
x_350 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace(x_1, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
x_123 = x_351;
x_124 = x_197;
x_125 = x_198;
x_126 = x_199;
x_127 = x_200;
x_128 = x_201;
x_129 = x_202;
x_130 = x_203;
x_131 = x_204;
x_132 = x_205;
x_133 = x_352;
goto block_159;
}
else
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
return x_350;
}
}
}
else
{
lean_object* x_353; 
lean_dec(x_331);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
x_353 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace(x_1, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_123 = x_354;
x_124 = x_197;
x_125 = x_198;
x_126 = x_199;
x_127 = x_200;
x_128 = x_201;
x_129 = x_202;
x_130 = x_203;
x_131 = x_204;
x_132 = x_205;
x_133 = x_355;
goto block_159;
}
else
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
return x_353;
}
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_331);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
x_356 = lean_unsigned_to_nat(0u);
x_357 = l_Lean_Syntax_getArg(x_1, x_356);
lean_dec(x_1);
x_358 = l_Lean_Syntax_getSepArgs(x_357);
lean_dec(x_357);
x_359 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore(x_358, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
return x_359;
}
}
else
{
lean_object* x_360; 
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_1);
x_360 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq(x_327, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
return x_360;
}
}
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; size_t x_364; lean_object* x_365; size_t x_366; lean_object* x_367; 
x_361 = lean_unsigned_to_nat(1u);
x_362 = l_Lean_Syntax_getArg(x_1, x_361);
x_363 = l_Lean_Syntax_getArgs(x_362);
lean_dec(x_362);
x_364 = lean_array_size(x_363);
x_365 = lean_unsigned_to_nat(0u);
x_366 = lean_usize_of_nat(x_365);
x_367 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl_spec__0(x_364, x_366, x_363);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; 
lean_inc(x_1);
x_368 = l_Lean_Syntax_getKind(x_1);
x_369 = lean_mk_string_unchecked("seq1", 4, 4);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_370 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_369);
x_371 = lean_name_eq(x_368, x_370);
lean_dec(x_370);
if (x_371 == 0)
{
lean_object* x_372; lean_object* x_373; uint8_t x_374; 
x_372 = lean_mk_string_unchecked("grindTrace", 10, 10);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_373 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_372);
x_374 = lean_name_eq(x_368, x_373);
lean_dec(x_373);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; uint8_t x_377; 
x_375 = lean_mk_string_unchecked("simpTrace", 9, 9);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
x_376 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_375);
x_377 = lean_name_eq(x_368, x_376);
lean_dec(x_376);
if (x_377 == 0)
{
lean_object* x_378; lean_object* x_379; uint8_t x_380; 
x_378 = lean_mk_string_unchecked("exact\?", 6, 6);
x_379 = l_Lean_Name_mkStr4(x_207, x_208, x_209, x_378);
x_380 = lean_name_eq(x_368, x_379);
lean_dec(x_379);
lean_dec(x_368);
if (x_380 == 0)
{
lean_object* x_381; 
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
x_381 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestDefault(x_1, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
x_160 = x_382;
x_161 = x_197;
x_162 = x_198;
x_163 = x_199;
x_164 = x_200;
x_165 = x_201;
x_166 = x_202;
x_167 = x_203;
x_168 = x_204;
x_169 = x_205;
x_170 = x_383;
goto block_196;
}
else
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
return x_381;
}
}
else
{
lean_object* x_384; 
lean_dec(x_1);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
x_384 = l_Lean_Elab_Tactic_Try_evalSuggestExact(x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec(x_384);
x_160 = x_385;
x_161 = x_197;
x_162 = x_198;
x_163 = x_199;
x_164 = x_200;
x_165 = x_201;
x_166 = x_202;
x_167 = x_203;
x_168 = x_204;
x_169 = x_205;
x_170 = x_386;
goto block_196;
}
else
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
return x_384;
}
}
}
else
{
lean_object* x_387; 
lean_dec(x_368);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
x_387 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace(x_1, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; 
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
lean_dec(x_387);
x_160 = x_388;
x_161 = x_197;
x_162 = x_198;
x_163 = x_199;
x_164 = x_200;
x_165 = x_201;
x_166 = x_202;
x_167 = x_203;
x_168 = x_204;
x_169 = x_205;
x_170 = x_389;
goto block_196;
}
else
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
return x_387;
}
}
}
else
{
lean_object* x_390; 
lean_dec(x_368);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
x_390 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace(x_1, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
x_160 = x_391;
x_161 = x_197;
x_162 = x_198;
x_163 = x_199;
x_164 = x_200;
x_165 = x_201;
x_166 = x_202;
x_167 = x_203;
x_168 = x_204;
x_169 = x_205;
x_170 = x_392;
goto block_196;
}
else
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
return x_390;
}
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_368);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
x_393 = l_Lean_Syntax_getArg(x_1, x_365);
lean_dec(x_1);
x_394 = l_Lean_Syntax_getSepArgs(x_393);
lean_dec(x_393);
x_395 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore(x_394, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
return x_395;
}
}
else
{
lean_object* x_396; lean_object* x_397; 
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_1);
x_396 = lean_ctor_get(x_367, 0);
lean_inc(x_396);
lean_dec(x_367);
x_397 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst(x_396, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
lean_dec(x_396);
return x_397;
}
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
x_398 = lean_unsigned_to_nat(0u);
x_399 = lean_unsigned_to_nat(2u);
x_400 = l_Lean_Syntax_getArg(x_1, x_399);
x_401 = l_Lean_Syntax_getArg(x_1, x_398);
lean_dec(x_1);
x_402 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain(x_401, x_400, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_206);
return x_402;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toSuggestion(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("tactic", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set(x_9, 3, x_6);
lean_ctor_set(x_9, 4, x_7);
lean_ctor_set(x_9, 5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestions_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toSuggestion(x_5);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestions(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; lean_object* x_4; size_t x_5; lean_object* x_6; 
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionsCore(x_1);
x_3 = lean_array_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestions_spec__0(x_3, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestions_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestions_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_mk_string_unchecked("try\?", 4, 4);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_mk_string_unchecked("consider using `grind` manually, or `try\? +missing` for partial proofs containing `sorry`", 89, 89);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_MessageData_ofFormat(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_Meta_throwTacticEx___redArg(x_16, x_13, x_20, x_6, x_7, x_8, x_9, x_14);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_mk_string_unchecked("try\?", 4, 4);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_mk_string_unchecked("consider using `grind` manually", 31, 31);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_MessageData_ofFormat(x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_Meta_throwTacticEx___redArg(x_25, x_22, x_29, x_6, x_7, x_8, x_9, x_23);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_11);
if (x_31 == 0)
{
return x_11;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_11, 0);
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_11);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; size_t x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_5, 5);
lean_inc(x_11);
x_12 = lean_array_size(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_usize_of_nat(x_13);
x_15 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions_spec__0(x_12, x_14, x_2);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_17 = lean_mk_string_unchecked("Try these:", 10, 10);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = l_Lean_Meta_Tactic_TryThis_addSuggestions(x_1, x_15, x_16, x_17, x_18, x_19, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_16);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_5, 5);
lean_inc(x_21);
x_22 = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion;
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get(x_22, x_2, x_23);
lean_dec(x_2);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_21);
x_26 = lean_mk_string_unchecked("Try this: ", 10, 10);
x_27 = lean_box(0);
x_28 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_24, x_25, x_26, x_27, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_25);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___redArg(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalAndSuggest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_29 = l_Lean_Elab_Tactic_saveState___redArg(x_5, x_7, x_9, x_10, x_11, x_12);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_box(1);
lean_inc(x_3);
lean_inc(x_2);
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_3);
x_34 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_34);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_35 = lean_eval_suggest_tactic(x_2, x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
if (lean_obj_tag(x_35) == 0)
{
lean_dec(x_30);
x_13 = x_35;
goto block_28;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_43; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
x_43 = l_Lean_Exception_isInterrupt(x_36);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = l_Lean_Exception_isRuntime(x_36);
lean_dec(x_36);
x_38 = x_44;
goto block_42;
}
else
{
lean_dec(x_36);
x_38 = x_43;
goto block_42;
}
block_42:
{
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_35);
x_39 = l_Lean_Elab_Tactic_SavedState_restore(x_30, x_38, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_37);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_40);
x_13 = x_41;
goto block_28;
}
else
{
lean_dec(x_37);
lean_dec(x_30);
x_13 = x_35;
goto block_28;
}
}
}
block_28:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestions(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_19 = l_Array_toSubarray___redArg(x_16, x_17, x_18);
x_20 = l_Array_ofSubarray___redArg(x_19);
lean_dec(x_19);
x_21 = l_Array_isEmpty___redArg(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___redArg(x_1, x_20, x_8, x_9, x_10, x_11, x_15);
lean_dec(x_9);
lean_dec(x_8);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_20);
x_23 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalAndSuggest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_Try_evalAndSuggest(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_unresolveNameGlobalAvoidingLocals___at___Lean_Elab_Tactic_mkSimpOnly_spec__0(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_mk_syntax_ident(x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_mk_syntax_ident(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; 
x_6 = lean_ctor_get(x_1, 5);
x_7 = lean_box(0);
x_8 = lean_mk_string_unchecked("null", 4, 4);
x_9 = lean_unbox(x_7);
x_10 = l_Lean_SourceInfo_fromRef(x_6, x_9);
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = l_Lean_Name_mkStr1(x_8);
x_15 = lean_box(0);
lean_inc(x_4);
x_16 = lean_array_uset(x_4, x_3, x_15);
x_17 = lean_mk_string_unchecked("group", 5, 5);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_10);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_22 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_21);
x_23 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
x_24 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_23);
x_25 = lean_array_uget(x_4, x_3);
lean_dec(x_4);
lean_inc(x_10);
x_26 = l_Lean_Syntax_node1(x_10, x_14, x_25);
lean_inc(x_10);
x_27 = l_Lean_Syntax_node1(x_10, x_24, x_26);
lean_inc(x_10);
x_28 = l_Lean_Syntax_node1(x_10, x_22, x_27);
x_29 = l_Lean_Syntax_node2(x_10, x_18, x_20, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_usize_of_nat(x_30);
x_32 = lean_usize_add(x_3, x_31);
x_33 = lean_array_uset(x_16, x_3, x_29);
x_3 = x_32;
x_4 = x_33;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_3, x_4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 5);
x_12 = l_Lean_SourceInfo_fromRef(x_11, x_7);
x_13 = lean_mk_string_unchecked("Lean", 4, 4);
x_14 = lean_mk_string_unchecked("Parser", 6, 6);
x_15 = lean_mk_string_unchecked("Tactic", 6, 6);
x_16 = lean_mk_string_unchecked("first", 5, 5);
lean_inc(x_16);
x_17 = l_Lean_Name_mkStr4(x_13, x_14, x_15, x_16);
lean_inc(x_12);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_mk_string_unchecked("null", 4, 4);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = l_Array_mkArray0(lean_box(0));
x_22 = lean_array_size(x_1);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_usize_of_nat(x_23);
x_25 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx_spec__0(x_2, x_22, x_24, x_1);
x_26 = l_Array_append(lean_box(0), x_21, x_25);
lean_dec(x_25);
lean_inc(x_12);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_20);
lean_ctor_set(x_27, 2, x_26);
x_28 = l_Lean_Syntax_node2(x_12, x_17, x_18, x_27);
lean_ctor_set(x_8, 0, x_28);
return x_8;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; lean_object* x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_ctor_get(x_2, 5);
x_31 = l_Lean_SourceInfo_fromRef(x_30, x_7);
x_32 = lean_mk_string_unchecked("Lean", 4, 4);
x_33 = lean_mk_string_unchecked("Parser", 6, 6);
x_34 = lean_mk_string_unchecked("Tactic", 6, 6);
x_35 = lean_mk_string_unchecked("first", 5, 5);
lean_inc(x_35);
x_36 = l_Lean_Name_mkStr4(x_32, x_33, x_34, x_35);
lean_inc(x_31);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_mk_string_unchecked("null", 4, 4);
x_39 = l_Lean_Name_mkStr1(x_38);
x_40 = l_Array_mkArray0(lean_box(0));
x_41 = lean_array_size(x_1);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_usize_of_nat(x_42);
x_44 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx_spec__0(x_2, x_41, x_43, x_1);
x_45 = l_Array_append(lean_box(0), x_40, x_44);
lean_dec(x_44);
lean_inc(x_31);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_31);
lean_ctor_set(x_46, 1, x_39);
lean_ctor_set(x_46, 2, x_45);
x_47 = l_Lean_Syntax_node2(x_31, x_36, x_37, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_29);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_mk_string_unchecked("tactic", 6, 6);
x_50 = l_Lean_Name_mkStr1(x_49);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_instInhabitedTSyntax(x_52);
lean_dec(x_52);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_array_get(x_53, x_1, x_54);
lean_dec(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_4);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_3 = lean_mk_string_unchecked("[", 1, 1);
x_4 = l_Lean_mkAtom(x_3);
x_5 = lean_mk_string_unchecked(",", 1, 1);
x_6 = l_Lean_mkAtom(x_5);
x_7 = l_Lean_Syntax_mkSep(x_2, x_6);
x_8 = lean_mk_string_unchecked("]", 1, 1);
x_9 = l_Lean_mkAtom(x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = lean_array_push(x_11, x_4);
x_13 = lean_array_push(x_12, x_7);
x_14 = lean_array_push(x_13, x_9);
x_15 = lean_mk_string_unchecked("null", 4, 4);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_box(2);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_14);
x_19 = l_Lean_Syntax_setArg(x_1, x_10, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_22; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toIdent(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_7, x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_6, 5);
lean_inc(x_29);
x_30 = lean_box(0);
x_31 = lean_unbox(x_30);
x_32 = l_Lean_SourceInfo_fromRef(x_29, x_31);
lean_dec(x_29);
x_33 = lean_mk_string_unchecked("Lean", 4, 4);
x_34 = lean_mk_string_unchecked("Parser", 6, 6);
x_35 = lean_mk_string_unchecked("Tactic", 6, 6);
x_36 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
x_37 = l_Lean_Name_mkStr4(x_33, x_34, x_35, x_36);
x_38 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_34);
lean_inc(x_33);
x_39 = l_Lean_Name_mkStr4(x_33, x_34, x_35, x_38);
x_40 = lean_mk_string_unchecked("null", 4, 4);
x_41 = l_Lean_Name_mkStr1(x_40);
x_42 = lean_mk_string_unchecked("Attr", 4, 4);
x_43 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_42);
lean_inc(x_34);
lean_inc(x_33);
x_44 = l_Lean_Name_mkStr4(x_33, x_34, x_42, x_43);
x_45 = lean_mk_string_unchecked("grindEq", 7, 7);
x_46 = l_Lean_Name_mkStr4(x_33, x_34, x_42, x_45);
x_47 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_32);
lean_ctor_set_tag(x_25, 2);
lean_ctor_set(x_25, 1, x_47);
lean_ctor_set(x_25, 0, x_32);
lean_inc(x_32);
x_48 = l_Lean_Syntax_node1(x_32, x_46, x_25);
lean_inc(x_32);
x_49 = l_Lean_Syntax_node1(x_32, x_44, x_48);
lean_inc(x_32);
x_50 = l_Lean_Syntax_node1(x_32, x_41, x_49);
lean_inc(x_32);
x_51 = l_Lean_Syntax_node2(x_32, x_39, x_50, x_23);
x_52 = l_Lean_Syntax_node1(x_32, x_37, x_51);
x_14 = x_52;
x_15 = x_27;
goto block_21;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_53 = lean_ctor_get(x_25, 1);
lean_inc(x_53);
lean_dec(x_25);
x_54 = lean_ctor_get(x_6, 5);
lean_inc(x_54);
x_55 = lean_box(0);
x_56 = lean_unbox(x_55);
x_57 = l_Lean_SourceInfo_fromRef(x_54, x_56);
lean_dec(x_54);
x_58 = lean_mk_string_unchecked("Lean", 4, 4);
x_59 = lean_mk_string_unchecked("Parser", 6, 6);
x_60 = lean_mk_string_unchecked("Tactic", 6, 6);
x_61 = lean_mk_string_unchecked("grindParam", 10, 10);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
x_62 = l_Lean_Name_mkStr4(x_58, x_59, x_60, x_61);
x_63 = lean_mk_string_unchecked("grindLemma", 10, 10);
lean_inc(x_59);
lean_inc(x_58);
x_64 = l_Lean_Name_mkStr4(x_58, x_59, x_60, x_63);
x_65 = lean_mk_string_unchecked("null", 4, 4);
x_66 = l_Lean_Name_mkStr1(x_65);
x_67 = lean_mk_string_unchecked("Attr", 4, 4);
x_68 = lean_mk_string_unchecked("grindMod", 8, 8);
lean_inc(x_67);
lean_inc(x_59);
lean_inc(x_58);
x_69 = l_Lean_Name_mkStr4(x_58, x_59, x_67, x_68);
x_70 = lean_mk_string_unchecked("grindEq", 7, 7);
x_71 = l_Lean_Name_mkStr4(x_58, x_59, x_67, x_70);
x_72 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_57);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_57);
lean_ctor_set(x_73, 1, x_72);
lean_inc(x_57);
x_74 = l_Lean_Syntax_node1(x_57, x_71, x_73);
lean_inc(x_57);
x_75 = l_Lean_Syntax_node1(x_57, x_69, x_74);
lean_inc(x_57);
x_76 = l_Lean_Syntax_node1(x_57, x_66, x_75);
lean_inc(x_57);
x_77 = l_Lean_Syntax_node2(x_57, x_64, x_76, x_23);
x_78 = l_Lean_Syntax_node1(x_57, x_62, x_77);
x_14 = x_78;
x_15 = x_53;
goto block_21;
}
}
else
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_22, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_22, 1);
lean_inc(x_80);
lean_dec(x_22);
x_14 = x_79;
x_15 = x_80;
goto block_21;
}
else
{
uint8_t x_81; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_81 = !lean_is_exclusive(x_22);
if (x_81 == 0)
{
return x_22;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_22, 0);
x_83 = lean_ctor_get(x_22, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_22);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
block_21:
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_13, x_2, x_14);
x_2 = x_18;
x_3 = x_19;
x_8 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_array_size(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_usize_of_nat(x_8);
x_10 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams_spec__0(x_7, x_9, x_1, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams_spec__0(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Try_Collector_OrdSet_isEmpty___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Array_isEmpty___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_4, 5);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_SourceInfo_fromRef(x_11, x_13);
lean_dec(x_11);
x_15 = lean_mk_string_unchecked("Lean", 4, 4);
x_16 = lean_mk_string_unchecked("Parser", 6, 6);
x_17 = lean_mk_string_unchecked("Tactic", 6, 6);
x_18 = lean_mk_string_unchecked("grindTrace", 10, 10);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_19 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_18);
x_20 = lean_mk_string_unchecked("grind\?", 6, 6);
lean_inc(x_14);
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_20);
lean_ctor_set(x_7, 0, x_14);
x_21 = lean_mk_string_unchecked("optConfig", 9, 9);
x_22 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_21);
x_23 = lean_mk_string_unchecked("null", 4, 4);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = l_Array_mkArray0(lean_box(0));
lean_inc(x_14);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
lean_inc(x_26);
lean_inc(x_14);
x_27 = l_Lean_Syntax_node1(x_14, x_22, x_26);
lean_inc_n(x_26, 2);
x_28 = l_Lean_Syntax_node5(x_14, x_19, x_7, x_27, x_26, x_26, x_26);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_mk_empty_array_with_capacity(x_50);
lean_inc(x_28);
x_52 = lean_array_push(x_51, x_28);
x_53 = lean_ctor_get(x_1, 2);
lean_inc(x_53);
x_54 = l_Lean_Meta_Try_Collector_OrdSet_isEmpty___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx_spec__0(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_56 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams(x_55, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_28);
x_59 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams(x_28, x_57);
lean_dec(x_57);
x_60 = lean_array_push(x_52, x_59);
x_29 = x_60;
x_30 = x_2;
x_31 = x_3;
x_32 = x_4;
x_33 = x_5;
x_34 = x_58;
goto block_49;
}
else
{
uint8_t x_61; 
lean_dec(x_52);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_56);
if (x_61 == 0)
{
return x_56;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_56, 0);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_56);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_dec(x_53);
x_29 = x_52;
x_30 = x_2;
x_31 = x_3;
x_32 = x_4;
x_33 = x_5;
x_34 = x_9;
goto block_49;
}
block_49:
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
lean_dec(x_1);
x_36 = l_Lean_Meta_Try_Collector_OrdSet_isEmpty___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx_spec__0(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_33);
lean_inc(x_32);
x_38 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams(x_37, x_30, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams(x_28, x_39);
lean_dec(x_39);
x_42 = lean_array_push(x_29, x_41);
x_43 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx(x_42, x_32, x_33, x_40);
lean_dec(x_33);
lean_dec(x_32);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_28);
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
else
{
lean_object* x_48; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
x_48 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx(x_29, x_32, x_33, x_34);
lean_dec(x_33);
lean_dec(x_32);
return x_48;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_65 = lean_ctor_get(x_7, 1);
lean_inc(x_65);
lean_dec(x_7);
x_66 = lean_ctor_get(x_4, 5);
lean_inc(x_66);
x_67 = lean_box(0);
x_68 = lean_unbox(x_67);
x_69 = l_Lean_SourceInfo_fromRef(x_66, x_68);
lean_dec(x_66);
x_70 = lean_mk_string_unchecked("Lean", 4, 4);
x_71 = lean_mk_string_unchecked("Parser", 6, 6);
x_72 = lean_mk_string_unchecked("Tactic", 6, 6);
x_73 = lean_mk_string_unchecked("grindTrace", 10, 10);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
x_74 = l_Lean_Name_mkStr4(x_70, x_71, x_72, x_73);
x_75 = lean_mk_string_unchecked("grind\?", 6, 6);
lean_inc(x_69);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_mk_string_unchecked("optConfig", 9, 9);
x_78 = l_Lean_Name_mkStr4(x_70, x_71, x_72, x_77);
x_79 = lean_mk_string_unchecked("null", 4, 4);
x_80 = l_Lean_Name_mkStr1(x_79);
x_81 = l_Array_mkArray0(lean_box(0));
lean_inc(x_69);
x_82 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_82, 0, x_69);
lean_ctor_set(x_82, 1, x_80);
lean_ctor_set(x_82, 2, x_81);
lean_inc(x_82);
lean_inc(x_69);
x_83 = l_Lean_Syntax_node1(x_69, x_78, x_82);
lean_inc_n(x_82, 2);
x_84 = l_Lean_Syntax_node5(x_69, x_74, x_76, x_83, x_82, x_82, x_82);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_mk_empty_array_with_capacity(x_106);
lean_inc(x_84);
x_108 = lean_array_push(x_107, x_84);
x_109 = lean_ctor_get(x_1, 2);
lean_inc(x_109);
x_110 = l_Lean_Meta_Try_Collector_OrdSet_isEmpty___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx_spec__0(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
lean_dec(x_109);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_112 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams(x_111, x_2, x_3, x_4, x_5, x_65);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
lean_inc(x_84);
x_115 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams(x_84, x_113);
lean_dec(x_113);
x_116 = lean_array_push(x_108, x_115);
x_85 = x_116;
x_86 = x_2;
x_87 = x_3;
x_88 = x_4;
x_89 = x_5;
x_90 = x_114;
goto block_105;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_108);
lean_dec(x_84);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_117 = lean_ctor_get(x_112, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_112, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_119 = x_112;
} else {
 lean_dec_ref(x_112);
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
lean_dec(x_109);
x_85 = x_108;
x_86 = x_2;
x_87 = x_3;
x_88 = x_4;
x_89 = x_5;
x_90 = x_65;
goto block_105;
}
block_105:
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_1, 1);
lean_inc(x_91);
lean_dec(x_1);
x_92 = l_Lean_Meta_Try_Collector_OrdSet_isEmpty___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx_spec__0(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
lean_dec(x_91);
lean_inc(x_89);
lean_inc(x_88);
x_94 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams(x_93, x_86, x_87, x_88, x_89, x_90);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams(x_84, x_95);
lean_dec(x_95);
x_98 = lean_array_push(x_85, x_97);
x_99 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx(x_98, x_88, x_89, x_96);
lean_dec(x_89);
lean_dec(x_88);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_85);
lean_dec(x_84);
x_100 = lean_ctor_get(x_94, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_94, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_102 = x_94;
} else {
 lean_dec_ref(x_94);
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
lean_object* x_104; 
lean_dec(x_91);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_84);
x_104 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx(x_85, x_88, x_89, x_90);
lean_dec(x_89);
lean_dec(x_88);
return x_104;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Try_Collector_OrdSet_isEmpty___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx_spec__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Try_Collector_OrdSet_isEmpty___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx_spec__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_6 = lean_ctor_get(x_4, 0);
lean_dec(x_6);
x_7 = lean_ctor_get(x_1, 5);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_SourceInfo_fromRef(x_7, x_9);
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = lean_mk_string_unchecked("first", 5, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_15 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_14);
lean_inc(x_10);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_mk_string_unchecked("null", 4, 4);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_mk_string_unchecked("group", 5, 5);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_10);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_24 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_23);
x_25 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_26 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_25);
x_27 = lean_mk_string_unchecked("simpTrace", 9, 9);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_28 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_27);
x_29 = lean_mk_string_unchecked("simp\?", 5, 5);
lean_inc(x_10);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Array_mkArray0(lean_box(0));
lean_inc(x_18);
lean_inc(x_10);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_10);
lean_ctor_set(x_32, 1, x_18);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_mk_string_unchecked("simpTraceArgsRest", 17, 17);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_34 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_33);
x_35 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_36 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_35);
lean_inc(x_32);
lean_inc(x_36);
lean_inc(x_10);
x_37 = l_Lean_Syntax_node1(x_10, x_36, x_32);
lean_inc_n(x_32, 4);
lean_inc(x_37);
lean_inc(x_34);
lean_inc(x_10);
x_38 = l_Lean_Syntax_node5(x_10, x_34, x_37, x_32, x_32, x_32, x_32);
lean_inc(x_32);
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_10);
x_39 = l_Lean_Syntax_node3(x_10, x_28, x_30, x_32, x_38);
lean_inc(x_18);
lean_inc(x_10);
x_40 = l_Lean_Syntax_node1(x_10, x_18, x_39);
lean_inc(x_26);
lean_inc(x_10);
x_41 = l_Lean_Syntax_node1(x_10, x_26, x_40);
lean_inc(x_24);
lean_inc(x_10);
x_42 = l_Lean_Syntax_node1(x_10, x_24, x_41);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_10);
x_43 = l_Lean_Syntax_node2(x_10, x_20, x_22, x_42);
x_44 = lean_mk_string_unchecked("simpArgs", 8, 8);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_45 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_44);
x_46 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_10);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_10);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("simpStar", 8, 8);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_49 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_48);
x_50 = lean_mk_string_unchecked("*", 1, 1);
lean_inc(x_10);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_10);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_10);
x_52 = l_Lean_Syntax_node1(x_10, x_49, x_51);
lean_inc(x_18);
lean_inc(x_10);
x_53 = l_Lean_Syntax_node1(x_10, x_18, x_52);
x_54 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_10);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_10);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_10);
x_56 = l_Lean_Syntax_node3(x_10, x_45, x_47, x_53, x_55);
lean_inc(x_18);
lean_inc(x_10);
x_57 = l_Lean_Syntax_node1(x_10, x_18, x_56);
lean_inc(x_57);
lean_inc_n(x_32, 3);
lean_inc(x_34);
lean_inc(x_10);
x_58 = l_Lean_Syntax_node5(x_10, x_34, x_37, x_32, x_32, x_57, x_32);
lean_inc(x_32);
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_10);
x_59 = l_Lean_Syntax_node3(x_10, x_28, x_30, x_32, x_58);
lean_inc(x_18);
lean_inc(x_10);
x_60 = l_Lean_Syntax_node1(x_10, x_18, x_59);
lean_inc(x_26);
lean_inc(x_10);
x_61 = l_Lean_Syntax_node1(x_10, x_26, x_60);
lean_inc(x_24);
lean_inc(x_10);
x_62 = l_Lean_Syntax_node1(x_10, x_24, x_61);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_10);
x_63 = l_Lean_Syntax_node2(x_10, x_20, x_22, x_62);
x_64 = lean_mk_string_unchecked("configItem", 10, 10);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_65 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_64);
x_66 = lean_mk_string_unchecked("posConfigItem", 13, 13);
x_67 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_66);
x_68 = lean_mk_string_unchecked("+", 1, 1);
lean_inc(x_10);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_10);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_mk_string_unchecked("arith", 5, 5);
lean_inc(x_70);
x_71 = l_String_toSubstring_x27(x_70);
x_72 = l_Lean_Name_mkStr1(x_70);
x_73 = lean_box(0);
lean_inc(x_10);
x_74 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_74, 0, x_10);
lean_ctor_set(x_74, 1, x_71);
lean_ctor_set(x_74, 2, x_72);
lean_ctor_set(x_74, 3, x_73);
lean_inc(x_10);
x_75 = l_Lean_Syntax_node2(x_10, x_67, x_69, x_74);
lean_inc(x_10);
x_76 = l_Lean_Syntax_node1(x_10, x_65, x_75);
lean_inc(x_18);
lean_inc(x_10);
x_77 = l_Lean_Syntax_node1(x_10, x_18, x_76);
lean_inc(x_10);
x_78 = l_Lean_Syntax_node1(x_10, x_36, x_77);
lean_inc_n(x_32, 4);
lean_inc(x_78);
lean_inc(x_34);
lean_inc(x_10);
x_79 = l_Lean_Syntax_node5(x_10, x_34, x_78, x_32, x_32, x_32, x_32);
lean_inc(x_32);
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_10);
x_80 = l_Lean_Syntax_node3(x_10, x_28, x_30, x_32, x_79);
lean_inc(x_18);
lean_inc(x_10);
x_81 = l_Lean_Syntax_node1(x_10, x_18, x_80);
lean_inc(x_26);
lean_inc(x_10);
x_82 = l_Lean_Syntax_node1(x_10, x_26, x_81);
lean_inc(x_24);
lean_inc(x_10);
x_83 = l_Lean_Syntax_node1(x_10, x_24, x_82);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_10);
x_84 = l_Lean_Syntax_node2(x_10, x_20, x_22, x_83);
lean_inc_n(x_32, 3);
lean_inc(x_10);
x_85 = l_Lean_Syntax_node5(x_10, x_34, x_78, x_32, x_32, x_57, x_32);
lean_inc(x_10);
x_86 = l_Lean_Syntax_node3(x_10, x_28, x_30, x_32, x_85);
lean_inc(x_18);
lean_inc(x_10);
x_87 = l_Lean_Syntax_node1(x_10, x_18, x_86);
lean_inc(x_10);
x_88 = l_Lean_Syntax_node1(x_10, x_26, x_87);
lean_inc(x_10);
x_89 = l_Lean_Syntax_node1(x_10, x_24, x_88);
lean_inc(x_10);
x_90 = l_Lean_Syntax_node2(x_10, x_20, x_22, x_89);
lean_inc(x_10);
x_91 = l_Lean_Syntax_node4(x_10, x_18, x_43, x_63, x_84, x_90);
x_92 = l_Lean_Syntax_node2(x_10, x_15, x_16, x_91);
lean_ctor_set(x_4, 0, x_92);
return x_4;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_93 = lean_ctor_get(x_4, 1);
lean_inc(x_93);
lean_dec(x_4);
x_94 = lean_ctor_get(x_1, 5);
x_95 = lean_box(0);
x_96 = lean_unbox(x_95);
x_97 = l_Lean_SourceInfo_fromRef(x_94, x_96);
x_98 = lean_mk_string_unchecked("Lean", 4, 4);
x_99 = lean_mk_string_unchecked("Parser", 6, 6);
x_100 = lean_mk_string_unchecked("Tactic", 6, 6);
x_101 = lean_mk_string_unchecked("first", 5, 5);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
x_102 = l_Lean_Name_mkStr4(x_98, x_99, x_100, x_101);
lean_inc(x_97);
x_103 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_103, 0, x_97);
lean_ctor_set(x_103, 1, x_101);
x_104 = lean_mk_string_unchecked("null", 4, 4);
x_105 = l_Lean_Name_mkStr1(x_104);
x_106 = lean_mk_string_unchecked("group", 5, 5);
x_107 = l_Lean_Name_mkStr1(x_106);
x_108 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_97);
x_109 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_109, 0, x_97);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
x_111 = l_Lean_Name_mkStr4(x_98, x_99, x_100, x_110);
x_112 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
x_113 = l_Lean_Name_mkStr4(x_98, x_99, x_100, x_112);
x_114 = lean_mk_string_unchecked("simpTrace", 9, 9);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
x_115 = l_Lean_Name_mkStr4(x_98, x_99, x_100, x_114);
x_116 = lean_mk_string_unchecked("simp\?", 5, 5);
lean_inc(x_97);
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_97);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Array_mkArray0(lean_box(0));
lean_inc(x_105);
lean_inc(x_97);
x_119 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_119, 0, x_97);
lean_ctor_set(x_119, 1, x_105);
lean_ctor_set(x_119, 2, x_118);
x_120 = lean_mk_string_unchecked("simpTraceArgsRest", 17, 17);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
x_121 = l_Lean_Name_mkStr4(x_98, x_99, x_100, x_120);
x_122 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
x_123 = l_Lean_Name_mkStr4(x_98, x_99, x_100, x_122);
lean_inc(x_119);
lean_inc(x_123);
lean_inc(x_97);
x_124 = l_Lean_Syntax_node1(x_97, x_123, x_119);
lean_inc_n(x_119, 4);
lean_inc(x_124);
lean_inc(x_121);
lean_inc(x_97);
x_125 = l_Lean_Syntax_node5(x_97, x_121, x_124, x_119, x_119, x_119, x_119);
lean_inc(x_119);
lean_inc(x_117);
lean_inc(x_115);
lean_inc(x_97);
x_126 = l_Lean_Syntax_node3(x_97, x_115, x_117, x_119, x_125);
lean_inc(x_105);
lean_inc(x_97);
x_127 = l_Lean_Syntax_node1(x_97, x_105, x_126);
lean_inc(x_113);
lean_inc(x_97);
x_128 = l_Lean_Syntax_node1(x_97, x_113, x_127);
lean_inc(x_111);
lean_inc(x_97);
x_129 = l_Lean_Syntax_node1(x_97, x_111, x_128);
lean_inc(x_109);
lean_inc(x_107);
lean_inc(x_97);
x_130 = l_Lean_Syntax_node2(x_97, x_107, x_109, x_129);
x_131 = lean_mk_string_unchecked("simpArgs", 8, 8);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
x_132 = l_Lean_Name_mkStr4(x_98, x_99, x_100, x_131);
x_133 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_97);
x_134 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_134, 0, x_97);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_mk_string_unchecked("simpStar", 8, 8);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
x_136 = l_Lean_Name_mkStr4(x_98, x_99, x_100, x_135);
x_137 = lean_mk_string_unchecked("*", 1, 1);
lean_inc(x_97);
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_97);
lean_ctor_set(x_138, 1, x_137);
lean_inc(x_97);
x_139 = l_Lean_Syntax_node1(x_97, x_136, x_138);
lean_inc(x_105);
lean_inc(x_97);
x_140 = l_Lean_Syntax_node1(x_97, x_105, x_139);
x_141 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_97);
x_142 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_142, 0, x_97);
lean_ctor_set(x_142, 1, x_141);
lean_inc(x_97);
x_143 = l_Lean_Syntax_node3(x_97, x_132, x_134, x_140, x_142);
lean_inc(x_105);
lean_inc(x_97);
x_144 = l_Lean_Syntax_node1(x_97, x_105, x_143);
lean_inc(x_144);
lean_inc_n(x_119, 3);
lean_inc(x_121);
lean_inc(x_97);
x_145 = l_Lean_Syntax_node5(x_97, x_121, x_124, x_119, x_119, x_144, x_119);
lean_inc(x_119);
lean_inc(x_117);
lean_inc(x_115);
lean_inc(x_97);
x_146 = l_Lean_Syntax_node3(x_97, x_115, x_117, x_119, x_145);
lean_inc(x_105);
lean_inc(x_97);
x_147 = l_Lean_Syntax_node1(x_97, x_105, x_146);
lean_inc(x_113);
lean_inc(x_97);
x_148 = l_Lean_Syntax_node1(x_97, x_113, x_147);
lean_inc(x_111);
lean_inc(x_97);
x_149 = l_Lean_Syntax_node1(x_97, x_111, x_148);
lean_inc(x_109);
lean_inc(x_107);
lean_inc(x_97);
x_150 = l_Lean_Syntax_node2(x_97, x_107, x_109, x_149);
x_151 = lean_mk_string_unchecked("configItem", 10, 10);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
x_152 = l_Lean_Name_mkStr4(x_98, x_99, x_100, x_151);
x_153 = lean_mk_string_unchecked("posConfigItem", 13, 13);
x_154 = l_Lean_Name_mkStr4(x_98, x_99, x_100, x_153);
x_155 = lean_mk_string_unchecked("+", 1, 1);
lean_inc(x_97);
x_156 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_156, 0, x_97);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_mk_string_unchecked("arith", 5, 5);
lean_inc(x_157);
x_158 = l_String_toSubstring_x27(x_157);
x_159 = l_Lean_Name_mkStr1(x_157);
x_160 = lean_box(0);
lean_inc(x_97);
x_161 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_161, 0, x_97);
lean_ctor_set(x_161, 1, x_158);
lean_ctor_set(x_161, 2, x_159);
lean_ctor_set(x_161, 3, x_160);
lean_inc(x_97);
x_162 = l_Lean_Syntax_node2(x_97, x_154, x_156, x_161);
lean_inc(x_97);
x_163 = l_Lean_Syntax_node1(x_97, x_152, x_162);
lean_inc(x_105);
lean_inc(x_97);
x_164 = l_Lean_Syntax_node1(x_97, x_105, x_163);
lean_inc(x_97);
x_165 = l_Lean_Syntax_node1(x_97, x_123, x_164);
lean_inc_n(x_119, 4);
lean_inc(x_165);
lean_inc(x_121);
lean_inc(x_97);
x_166 = l_Lean_Syntax_node5(x_97, x_121, x_165, x_119, x_119, x_119, x_119);
lean_inc(x_119);
lean_inc(x_117);
lean_inc(x_115);
lean_inc(x_97);
x_167 = l_Lean_Syntax_node3(x_97, x_115, x_117, x_119, x_166);
lean_inc(x_105);
lean_inc(x_97);
x_168 = l_Lean_Syntax_node1(x_97, x_105, x_167);
lean_inc(x_113);
lean_inc(x_97);
x_169 = l_Lean_Syntax_node1(x_97, x_113, x_168);
lean_inc(x_111);
lean_inc(x_97);
x_170 = l_Lean_Syntax_node1(x_97, x_111, x_169);
lean_inc(x_109);
lean_inc(x_107);
lean_inc(x_97);
x_171 = l_Lean_Syntax_node2(x_97, x_107, x_109, x_170);
lean_inc_n(x_119, 3);
lean_inc(x_97);
x_172 = l_Lean_Syntax_node5(x_97, x_121, x_165, x_119, x_119, x_144, x_119);
lean_inc(x_97);
x_173 = l_Lean_Syntax_node3(x_97, x_115, x_117, x_119, x_172);
lean_inc(x_105);
lean_inc(x_97);
x_174 = l_Lean_Syntax_node1(x_97, x_105, x_173);
lean_inc(x_97);
x_175 = l_Lean_Syntax_node1(x_97, x_113, x_174);
lean_inc(x_97);
x_176 = l_Lean_Syntax_node1(x_97, x_111, x_175);
lean_inc(x_97);
x_177 = l_Lean_Syntax_node2(x_97, x_107, x_109, x_176);
lean_inc(x_97);
x_178 = l_Lean_Syntax_node4(x_97, x_105, x_130, x_150, x_171, x_177);
x_179 = l_Lean_Syntax_node2(x_97, x_102, x_103, x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_93);
return x_180;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_6 = lean_ctor_get(x_4, 0);
lean_dec(x_6);
x_7 = lean_ctor_get(x_1, 5);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_SourceInfo_fromRef(x_7, x_9);
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = lean_mk_string_unchecked("attemptAll", 10, 10);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_15 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_14);
x_16 = lean_mk_string_unchecked("attempt_all", 11, 11);
lean_inc(x_10);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_mk_string_unchecked("null", 4, 4);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = lean_mk_string_unchecked("group", 5, 5);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_10);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_25 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_24);
x_26 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_27 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_26);
x_28 = lean_mk_string_unchecked("tacticRfl", 9, 9);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_29 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_28);
x_30 = lean_mk_string_unchecked("rfl", 3, 3);
lean_inc(x_10);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_10);
lean_ctor_set(x_31, 1, x_30);
lean_inc(x_10);
x_32 = l_Lean_Syntax_node1(x_10, x_29, x_31);
lean_inc(x_19);
lean_inc(x_10);
x_33 = l_Lean_Syntax_node1(x_10, x_19, x_32);
lean_inc(x_27);
lean_inc(x_10);
x_34 = l_Lean_Syntax_node1(x_10, x_27, x_33);
lean_inc(x_25);
lean_inc(x_10);
x_35 = l_Lean_Syntax_node1(x_10, x_25, x_34);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_10);
x_36 = l_Lean_Syntax_node2(x_10, x_21, x_23, x_35);
x_37 = lean_mk_string_unchecked("assumption", 10, 10);
lean_inc(x_37);
x_38 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_37);
lean_inc(x_10);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_10);
lean_ctor_set(x_39, 1, x_37);
lean_inc(x_10);
x_40 = l_Lean_Syntax_node1(x_10, x_38, x_39);
lean_inc(x_19);
lean_inc(x_10);
x_41 = l_Lean_Syntax_node1(x_10, x_19, x_40);
lean_inc(x_10);
x_42 = l_Lean_Syntax_node1(x_10, x_27, x_41);
lean_inc(x_10);
x_43 = l_Lean_Syntax_node1(x_10, x_25, x_42);
lean_inc(x_10);
x_44 = l_Lean_Syntax_node2(x_10, x_21, x_23, x_43);
lean_inc(x_10);
x_45 = l_Lean_Syntax_node2(x_10, x_19, x_36, x_44);
x_46 = l_Lean_Syntax_node2(x_10, x_15, x_17, x_45);
lean_ctor_set(x_4, 0, x_46);
return x_4;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_47 = lean_ctor_get(x_4, 1);
lean_inc(x_47);
lean_dec(x_4);
x_48 = lean_ctor_get(x_1, 5);
x_49 = lean_box(0);
x_50 = lean_unbox(x_49);
x_51 = l_Lean_SourceInfo_fromRef(x_48, x_50);
x_52 = lean_mk_string_unchecked("Lean", 4, 4);
x_53 = lean_mk_string_unchecked("Parser", 6, 6);
x_54 = lean_mk_string_unchecked("Tactic", 6, 6);
x_55 = lean_mk_string_unchecked("attemptAll", 10, 10);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
x_56 = l_Lean_Name_mkStr4(x_52, x_53, x_54, x_55);
x_57 = lean_mk_string_unchecked("attempt_all", 11, 11);
lean_inc(x_51);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_mk_string_unchecked("null", 4, 4);
x_60 = l_Lean_Name_mkStr1(x_59);
x_61 = lean_mk_string_unchecked("group", 5, 5);
x_62 = l_Lean_Name_mkStr1(x_61);
x_63 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_51);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_51);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
x_66 = l_Lean_Name_mkStr4(x_52, x_53, x_54, x_65);
x_67 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
x_68 = l_Lean_Name_mkStr4(x_52, x_53, x_54, x_67);
x_69 = lean_mk_string_unchecked("tacticRfl", 9, 9);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
x_70 = l_Lean_Name_mkStr4(x_52, x_53, x_54, x_69);
x_71 = lean_mk_string_unchecked("rfl", 3, 3);
lean_inc(x_51);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_51);
lean_ctor_set(x_72, 1, x_71);
lean_inc(x_51);
x_73 = l_Lean_Syntax_node1(x_51, x_70, x_72);
lean_inc(x_60);
lean_inc(x_51);
x_74 = l_Lean_Syntax_node1(x_51, x_60, x_73);
lean_inc(x_68);
lean_inc(x_51);
x_75 = l_Lean_Syntax_node1(x_51, x_68, x_74);
lean_inc(x_66);
lean_inc(x_51);
x_76 = l_Lean_Syntax_node1(x_51, x_66, x_75);
lean_inc(x_64);
lean_inc(x_62);
lean_inc(x_51);
x_77 = l_Lean_Syntax_node2(x_51, x_62, x_64, x_76);
x_78 = lean_mk_string_unchecked("assumption", 10, 10);
lean_inc(x_78);
x_79 = l_Lean_Name_mkStr4(x_52, x_53, x_54, x_78);
lean_inc(x_51);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_51);
lean_ctor_set(x_80, 1, x_78);
lean_inc(x_51);
x_81 = l_Lean_Syntax_node1(x_51, x_79, x_80);
lean_inc(x_60);
lean_inc(x_51);
x_82 = l_Lean_Syntax_node1(x_51, x_60, x_81);
lean_inc(x_51);
x_83 = l_Lean_Syntax_node1(x_51, x_68, x_82);
lean_inc(x_51);
x_84 = l_Lean_Syntax_node1(x_51, x_66, x_83);
lean_inc(x_51);
x_85 = l_Lean_Syntax_node2(x_51, x_62, x_64, x_84);
lean_inc(x_51);
x_86 = l_Lean_Syntax_node2(x_51, x_60, x_77, x_85);
x_87 = l_Lean_Syntax_node2(x_51, x_56, x_58, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_47);
return x_88;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
x_11 = l_Lean_PrettyPrinter_delab(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_st_ref_get(x_9, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_8, 5);
lean_inc(x_19);
x_20 = l_Lean_SourceInfo_fromRef(x_19, x_3);
x_21 = lean_mk_string_unchecked("Lean", 4, 4);
x_22 = lean_mk_string_unchecked("Parser", 6, 6);
x_23 = lean_mk_string_unchecked("Tactic", 6, 6);
x_24 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_25 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_24);
x_26 = lean_mk_string_unchecked("funInduction", 12, 12);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_27 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_26);
x_28 = lean_mk_string_unchecked("fun_induction", 13, 13);
lean_inc(x_20);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_28);
lean_ctor_set(x_11, 0, x_20);
x_29 = lean_mk_string_unchecked("null", 4, 4);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = l_Array_mkArray0(lean_box(0));
lean_inc(x_30);
lean_inc(x_20);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
lean_inc(x_32);
lean_inc(x_20);
x_33 = l_Lean_Syntax_node4(x_20, x_27, x_11, x_13, x_32, x_32);
x_34 = lean_mk_string_unchecked("<;>", 3, 3);
lean_inc(x_20);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_20);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Syntax_node3(x_20, x_25, x_33, x_35, x_4);
if (x_5 == 0)
{
lean_object* x_37; uint8_t x_38; 
lean_free_object(x_15);
x_37 = lean_st_ref_get(x_9, x_17);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_39 = lean_ctor_get(x_37, 1);
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = l_Lean_SourceInfo_fromRef(x_19, x_5);
lean_dec(x_19);
x_42 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_43 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_42);
x_44 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_41);
lean_ctor_set_tag(x_37, 2);
lean_ctor_set(x_37, 1, x_44);
lean_ctor_set(x_37, 0, x_41);
x_45 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_46 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_45);
x_47 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_48 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_47);
x_49 = lean_mk_string_unchecked("exposeNames", 11, 11);
x_50 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_49);
x_51 = lean_mk_string_unchecked("expose_names", 12, 12);
lean_inc(x_41);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_41);
x_53 = l_Lean_Syntax_node1(x_41, x_50, x_52);
x_54 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_41);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_41);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_36);
lean_inc(x_41);
x_56 = l_Lean_Syntax_node3(x_41, x_30, x_53, x_55, x_36);
lean_inc(x_41);
x_57 = l_Lean_Syntax_node1(x_41, x_48, x_56);
lean_inc(x_41);
x_58 = l_Lean_Syntax_node1(x_41, x_46, x_57);
x_59 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_41);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_41);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Syntax_node3(x_41, x_43, x_37, x_58, x_60);
x_62 = lean_unsigned_to_nat(2u);
x_63 = lean_mk_empty_array_with_capacity(x_62);
x_64 = lean_array_push(x_63, x_36);
x_65 = lean_array_push(x_64, x_61);
x_66 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx(x_65, x_8, x_9, x_39);
lean_dec(x_9);
lean_dec(x_8);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_67 = lean_ctor_get(x_37, 1);
lean_inc(x_67);
lean_dec(x_37);
x_68 = l_Lean_SourceInfo_fromRef(x_19, x_5);
lean_dec(x_19);
x_69 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_70 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_69);
x_71 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_68);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_74 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_73);
x_75 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_76 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_75);
x_77 = lean_mk_string_unchecked("exposeNames", 11, 11);
x_78 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_77);
x_79 = lean_mk_string_unchecked("expose_names", 12, 12);
lean_inc(x_68);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_68);
lean_ctor_set(x_80, 1, x_79);
lean_inc(x_68);
x_81 = l_Lean_Syntax_node1(x_68, x_78, x_80);
x_82 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_68);
x_83 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_83, 0, x_68);
lean_ctor_set(x_83, 1, x_82);
lean_inc(x_36);
lean_inc(x_68);
x_84 = l_Lean_Syntax_node3(x_68, x_30, x_81, x_83, x_36);
lean_inc(x_68);
x_85 = l_Lean_Syntax_node1(x_68, x_76, x_84);
lean_inc(x_68);
x_86 = l_Lean_Syntax_node1(x_68, x_74, x_85);
x_87 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_68);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_68);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_Syntax_node3(x_68, x_70, x_72, x_86, x_88);
x_90 = lean_unsigned_to_nat(2u);
x_91 = lean_mk_empty_array_with_capacity(x_90);
x_92 = lean_array_push(x_91, x_36);
x_93 = lean_array_push(x_92, x_89);
x_94 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx(x_93, x_8, x_9, x_67);
lean_dec(x_9);
lean_dec(x_8);
return x_94;
}
}
else
{
lean_dec(x_30);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_ctor_set(x_15, 0, x_36);
return x_15;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_95 = lean_ctor_get(x_15, 1);
lean_inc(x_95);
lean_dec(x_15);
x_96 = lean_ctor_get(x_8, 5);
lean_inc(x_96);
x_97 = l_Lean_SourceInfo_fromRef(x_96, x_3);
x_98 = lean_mk_string_unchecked("Lean", 4, 4);
x_99 = lean_mk_string_unchecked("Parser", 6, 6);
x_100 = lean_mk_string_unchecked("Tactic", 6, 6);
x_101 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
x_102 = l_Lean_Name_mkStr4(x_98, x_99, x_100, x_101);
x_103 = lean_mk_string_unchecked("funInduction", 12, 12);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
x_104 = l_Lean_Name_mkStr4(x_98, x_99, x_100, x_103);
x_105 = lean_mk_string_unchecked("fun_induction", 13, 13);
lean_inc(x_97);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_105);
lean_ctor_set(x_11, 0, x_97);
x_106 = lean_mk_string_unchecked("null", 4, 4);
x_107 = l_Lean_Name_mkStr1(x_106);
x_108 = l_Array_mkArray0(lean_box(0));
lean_inc(x_107);
lean_inc(x_97);
x_109 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_109, 0, x_97);
lean_ctor_set(x_109, 1, x_107);
lean_ctor_set(x_109, 2, x_108);
lean_inc(x_109);
lean_inc(x_97);
x_110 = l_Lean_Syntax_node4(x_97, x_104, x_11, x_13, x_109, x_109);
x_111 = lean_mk_string_unchecked("<;>", 3, 3);
lean_inc(x_97);
x_112 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_112, 0, x_97);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_Syntax_node3(x_97, x_102, x_110, x_112, x_4);
if (x_5 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_114 = lean_st_ref_get(x_9, x_95);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
x_117 = l_Lean_SourceInfo_fromRef(x_96, x_5);
lean_dec(x_96);
x_118 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
x_119 = l_Lean_Name_mkStr4(x_98, x_99, x_100, x_118);
x_120 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_117);
if (lean_is_scalar(x_116)) {
 x_121 = lean_alloc_ctor(2, 2, 0);
} else {
 x_121 = x_116;
 lean_ctor_set_tag(x_121, 2);
}
lean_ctor_set(x_121, 0, x_117);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
x_123 = l_Lean_Name_mkStr4(x_98, x_99, x_100, x_122);
x_124 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
x_125 = l_Lean_Name_mkStr4(x_98, x_99, x_100, x_124);
x_126 = lean_mk_string_unchecked("exposeNames", 11, 11);
x_127 = l_Lean_Name_mkStr4(x_98, x_99, x_100, x_126);
x_128 = lean_mk_string_unchecked("expose_names", 12, 12);
lean_inc(x_117);
x_129 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_129, 0, x_117);
lean_ctor_set(x_129, 1, x_128);
lean_inc(x_117);
x_130 = l_Lean_Syntax_node1(x_117, x_127, x_129);
x_131 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_117);
x_132 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_132, 0, x_117);
lean_ctor_set(x_132, 1, x_131);
lean_inc(x_113);
lean_inc(x_117);
x_133 = l_Lean_Syntax_node3(x_117, x_107, x_130, x_132, x_113);
lean_inc(x_117);
x_134 = l_Lean_Syntax_node1(x_117, x_125, x_133);
lean_inc(x_117);
x_135 = l_Lean_Syntax_node1(x_117, x_123, x_134);
x_136 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_117);
x_137 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_137, 0, x_117);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_Syntax_node3(x_117, x_119, x_121, x_135, x_137);
x_139 = lean_unsigned_to_nat(2u);
x_140 = lean_mk_empty_array_with_capacity(x_139);
x_141 = lean_array_push(x_140, x_113);
x_142 = lean_array_push(x_141, x_138);
x_143 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx(x_142, x_8, x_9, x_115);
lean_dec(x_9);
lean_dec(x_8);
return x_143;
}
else
{
lean_object* x_144; 
lean_dec(x_107);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_9);
lean_dec(x_8);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_113);
lean_ctor_set(x_144, 1, x_95);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_145 = lean_ctor_get(x_11, 0);
x_146 = lean_ctor_get(x_11, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_11);
x_147 = lean_st_ref_get(x_9, x_146);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_149 = x_147;
} else {
 lean_dec_ref(x_147);
 x_149 = lean_box(0);
}
x_150 = lean_ctor_get(x_8, 5);
lean_inc(x_150);
x_151 = l_Lean_SourceInfo_fromRef(x_150, x_3);
x_152 = lean_mk_string_unchecked("Lean", 4, 4);
x_153 = lean_mk_string_unchecked("Parser", 6, 6);
x_154 = lean_mk_string_unchecked("Tactic", 6, 6);
x_155 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
x_156 = l_Lean_Name_mkStr4(x_152, x_153, x_154, x_155);
x_157 = lean_mk_string_unchecked("funInduction", 12, 12);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
x_158 = l_Lean_Name_mkStr4(x_152, x_153, x_154, x_157);
x_159 = lean_mk_string_unchecked("fun_induction", 13, 13);
lean_inc(x_151);
x_160 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_160, 0, x_151);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_mk_string_unchecked("null", 4, 4);
x_162 = l_Lean_Name_mkStr1(x_161);
x_163 = l_Array_mkArray0(lean_box(0));
lean_inc(x_162);
lean_inc(x_151);
x_164 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_164, 0, x_151);
lean_ctor_set(x_164, 1, x_162);
lean_ctor_set(x_164, 2, x_163);
lean_inc(x_164);
lean_inc(x_151);
x_165 = l_Lean_Syntax_node4(x_151, x_158, x_160, x_145, x_164, x_164);
x_166 = lean_mk_string_unchecked("<;>", 3, 3);
lean_inc(x_151);
x_167 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_167, 0, x_151);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lean_Syntax_node3(x_151, x_156, x_165, x_167, x_4);
if (x_5 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_149);
x_169 = lean_st_ref_get(x_9, x_148);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_171 = x_169;
} else {
 lean_dec_ref(x_169);
 x_171 = lean_box(0);
}
x_172 = l_Lean_SourceInfo_fromRef(x_150, x_5);
lean_dec(x_150);
x_173 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
x_174 = l_Lean_Name_mkStr4(x_152, x_153, x_154, x_173);
x_175 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_172);
if (lean_is_scalar(x_171)) {
 x_176 = lean_alloc_ctor(2, 2, 0);
} else {
 x_176 = x_171;
 lean_ctor_set_tag(x_176, 2);
}
lean_ctor_set(x_176, 0, x_172);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
x_178 = l_Lean_Name_mkStr4(x_152, x_153, x_154, x_177);
x_179 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
x_180 = l_Lean_Name_mkStr4(x_152, x_153, x_154, x_179);
x_181 = lean_mk_string_unchecked("exposeNames", 11, 11);
x_182 = l_Lean_Name_mkStr4(x_152, x_153, x_154, x_181);
x_183 = lean_mk_string_unchecked("expose_names", 12, 12);
lean_inc(x_172);
x_184 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_184, 0, x_172);
lean_ctor_set(x_184, 1, x_183);
lean_inc(x_172);
x_185 = l_Lean_Syntax_node1(x_172, x_182, x_184);
x_186 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_172);
x_187 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_187, 0, x_172);
lean_ctor_set(x_187, 1, x_186);
lean_inc(x_168);
lean_inc(x_172);
x_188 = l_Lean_Syntax_node3(x_172, x_162, x_185, x_187, x_168);
lean_inc(x_172);
x_189 = l_Lean_Syntax_node1(x_172, x_180, x_188);
lean_inc(x_172);
x_190 = l_Lean_Syntax_node1(x_172, x_178, x_189);
x_191 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_172);
x_192 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_192, 0, x_172);
lean_ctor_set(x_192, 1, x_191);
x_193 = l_Lean_Syntax_node3(x_172, x_174, x_176, x_190, x_192);
x_194 = lean_unsigned_to_nat(2u);
x_195 = lean_mk_empty_array_with_capacity(x_194);
x_196 = lean_array_push(x_195, x_168);
x_197 = lean_array_push(x_196, x_193);
x_198 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx(x_197, x_8, x_9, x_170);
lean_dec(x_9);
lean_dec(x_8);
return x_198;
}
else
{
lean_object* x_199; 
lean_dec(x_162);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_9);
lean_dec(x_8);
if (lean_is_scalar(x_149)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_149;
}
lean_ctor_set(x_199, 0, x_168);
lean_ctor_set(x_199, 1, x_148);
return x_199;
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Expr_getAppFn(x_2);
x_10 = l_Lean_Expr_constName_x21(x_9);
lean_dec(x_9);
x_11 = l_Lean_NameSet_contains(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_inc(x_4);
lean_inc(x_2);
x_12 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_box(x_11);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lam__0___boxed), 10, 5);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_15);
lean_closure_set(x_17, 2, x_16);
lean_closure_set(x_17, 3, x_3);
lean_closure_set(x_17, 4, x_13);
x_18 = l_Lean_Meta_withExposedNames___redArg(x_17, x_4, x_5, x_6, x_7, x_14);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
lean_object* x_23; 
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
x_23 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toIdent(x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_st_ref_get(x_7, x_26);
lean_dec(x_7);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_6, 5);
lean_inc(x_30);
lean_dec(x_6);
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
x_33 = l_Lean_SourceInfo_fromRef(x_30, x_32);
lean_dec(x_30);
x_34 = lean_mk_string_unchecked("Lean", 4, 4);
x_35 = lean_mk_string_unchecked("Parser", 6, 6);
x_36 = lean_mk_string_unchecked("Tactic", 6, 6);
x_37 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
x_38 = l_Lean_Name_mkStr4(x_34, x_35, x_36, x_37);
x_39 = lean_mk_string_unchecked("funInduction", 12, 12);
x_40 = l_Lean_Name_mkStr4(x_34, x_35, x_36, x_39);
x_41 = lean_mk_string_unchecked("fun_induction", 13, 13);
lean_inc(x_33);
lean_ctor_set_tag(x_23, 2);
lean_ctor_set(x_23, 1, x_41);
lean_ctor_set(x_23, 0, x_33);
x_42 = lean_mk_string_unchecked("null", 4, 4);
x_43 = l_Lean_Name_mkStr1(x_42);
x_44 = l_Array_mkArray0(lean_box(0));
lean_inc(x_33);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_44);
lean_inc(x_45);
lean_inc(x_33);
x_46 = l_Lean_Syntax_node4(x_33, x_40, x_23, x_25, x_45, x_45);
x_47 = lean_mk_string_unchecked("<;>", 3, 3);
lean_inc(x_33);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_33);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Syntax_node3(x_33, x_38, x_46, x_48, x_3);
lean_ctor_set(x_27, 0, x_49);
return x_27;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_50 = lean_ctor_get(x_27, 1);
lean_inc(x_50);
lean_dec(x_27);
x_51 = lean_ctor_get(x_6, 5);
lean_inc(x_51);
lean_dec(x_6);
x_52 = lean_box(0);
x_53 = lean_unbox(x_52);
x_54 = l_Lean_SourceInfo_fromRef(x_51, x_53);
lean_dec(x_51);
x_55 = lean_mk_string_unchecked("Lean", 4, 4);
x_56 = lean_mk_string_unchecked("Parser", 6, 6);
x_57 = lean_mk_string_unchecked("Tactic", 6, 6);
x_58 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_59 = l_Lean_Name_mkStr4(x_55, x_56, x_57, x_58);
x_60 = lean_mk_string_unchecked("funInduction", 12, 12);
x_61 = l_Lean_Name_mkStr4(x_55, x_56, x_57, x_60);
x_62 = lean_mk_string_unchecked("fun_induction", 13, 13);
lean_inc(x_54);
lean_ctor_set_tag(x_23, 2);
lean_ctor_set(x_23, 1, x_62);
lean_ctor_set(x_23, 0, x_54);
x_63 = lean_mk_string_unchecked("null", 4, 4);
x_64 = l_Lean_Name_mkStr1(x_63);
x_65 = l_Array_mkArray0(lean_box(0));
lean_inc(x_54);
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_66, 2, x_65);
lean_inc(x_66);
lean_inc(x_54);
x_67 = l_Lean_Syntax_node4(x_54, x_61, x_23, x_25, x_66, x_66);
x_68 = lean_mk_string_unchecked("<;>", 3, 3);
lean_inc(x_54);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_54);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Syntax_node3(x_54, x_59, x_67, x_69, x_3);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_50);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_72 = lean_ctor_get(x_23, 0);
x_73 = lean_ctor_get(x_23, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_23);
x_74 = lean_st_ref_get(x_7, x_73);
lean_dec(x_7);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_6, 5);
lean_inc(x_77);
lean_dec(x_6);
x_78 = lean_box(0);
x_79 = lean_unbox(x_78);
x_80 = l_Lean_SourceInfo_fromRef(x_77, x_79);
lean_dec(x_77);
x_81 = lean_mk_string_unchecked("Lean", 4, 4);
x_82 = lean_mk_string_unchecked("Parser", 6, 6);
x_83 = lean_mk_string_unchecked("Tactic", 6, 6);
x_84 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
x_85 = l_Lean_Name_mkStr4(x_81, x_82, x_83, x_84);
x_86 = lean_mk_string_unchecked("funInduction", 12, 12);
x_87 = l_Lean_Name_mkStr4(x_81, x_82, x_83, x_86);
x_88 = lean_mk_string_unchecked("fun_induction", 13, 13);
lean_inc(x_80);
x_89 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_89, 0, x_80);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_mk_string_unchecked("null", 4, 4);
x_91 = l_Lean_Name_mkStr1(x_90);
x_92 = l_Array_mkArray0(lean_box(0));
lean_inc(x_80);
x_93 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_93, 0, x_80);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set(x_93, 2, x_92);
lean_inc(x_93);
lean_inc(x_80);
x_94 = l_Lean_Syntax_node4(x_80, x_87, x_89, x_72, x_93, x_93);
x_95 = lean_mk_string_unchecked("<;>", 3, 3);
lean_inc(x_80);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_80);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_Syntax_node3(x_80, x_85, x_94, x_96, x_3);
if (lean_is_scalar(x_76)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_76;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_75);
return x_98;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lam__0(x_1, x_2, x_11, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 3);
x_14 = l_Lean_Meta_FunInd_SeenCalls_uniques(x_13);
x_15 = lean_array_uget(x_5, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_16 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx(x_14, x_15, x_2, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_array_uset(x_5, x_4, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_add(x_4, x_22);
x_24 = lean_array_uset(x_20, x_4, x_17);
x_4 = x_23;
x_5 = x_24;
x_10 = x_18;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; size_t x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_array_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_usize_of_nat(x_11);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx_spec__0(x_1, x_2, x_10, x_12, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx(x_14, x_5, x_6, x_15);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_6);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_SourceInfo_fromRef(x_6, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx(x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx(x_4, x_5, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx(x_1, x_2, x_3, x_4, x_5, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_st_ref_get(x_5, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_21 = lean_ctor_get(x_19, 1);
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 5);
lean_inc(x_23);
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_SourceInfo_fromRef(x_23, x_25);
lean_dec(x_23);
x_27 = lean_mk_string_unchecked("Lean", 4, 4);
x_28 = lean_mk_string_unchecked("Parser", 6, 6);
x_29 = lean_mk_string_unchecked("Tactic", 6, 6);
x_30 = lean_mk_string_unchecked("attemptAll", 10, 10);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_31 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_30);
x_32 = lean_mk_string_unchecked("attempt_all", 11, 11);
lean_inc(x_26);
lean_ctor_set_tag(x_19, 2);
lean_ctor_set(x_19, 1, x_32);
lean_ctor_set(x_19, 0, x_26);
x_33 = lean_mk_string_unchecked("null", 4, 4);
x_34 = l_Lean_Name_mkStr1(x_33);
x_35 = lean_mk_string_unchecked("group", 5, 5);
x_36 = l_Lean_Name_mkStr1(x_35);
x_37 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_37);
lean_inc(x_26);
lean_ctor_set_tag(x_15, 2);
lean_ctor_set(x_15, 1, x_37);
lean_ctor_set(x_15, 0, x_26);
x_38 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_39 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_38);
x_40 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_41 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_40);
lean_inc(x_9);
lean_inc(x_34);
lean_inc(x_26);
x_42 = l_Lean_Syntax_node1(x_26, x_34, x_9);
lean_inc(x_41);
lean_inc(x_26);
x_43 = l_Lean_Syntax_node1(x_26, x_41, x_42);
lean_inc(x_39);
lean_inc(x_26);
x_44 = l_Lean_Syntax_node1(x_26, x_39, x_43);
lean_inc(x_15);
lean_inc(x_36);
lean_inc(x_26);
x_45 = l_Lean_Syntax_node2(x_26, x_36, x_15, x_44);
lean_inc(x_13);
lean_inc(x_34);
lean_inc(x_26);
x_46 = l_Lean_Syntax_node1(x_26, x_34, x_13);
lean_inc(x_41);
lean_inc(x_26);
x_47 = l_Lean_Syntax_node1(x_26, x_41, x_46);
lean_inc(x_39);
lean_inc(x_26);
x_48 = l_Lean_Syntax_node1(x_26, x_39, x_47);
lean_inc(x_15);
lean_inc(x_36);
lean_inc(x_26);
x_49 = l_Lean_Syntax_node2(x_26, x_36, x_15, x_48);
lean_inc(x_34);
lean_inc(x_26);
x_50 = l_Lean_Syntax_node1(x_26, x_34, x_17);
lean_inc(x_41);
lean_inc(x_26);
x_51 = l_Lean_Syntax_node1(x_26, x_41, x_50);
lean_inc(x_39);
lean_inc(x_26);
x_52 = l_Lean_Syntax_node1(x_26, x_39, x_51);
lean_inc(x_15);
lean_inc(x_36);
lean_inc(x_26);
x_53 = l_Lean_Syntax_node2(x_26, x_36, x_15, x_52);
x_54 = lean_mk_string_unchecked("simpAll", 7, 7);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_55 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_54);
x_56 = lean_mk_string_unchecked("simp_all", 8, 8);
lean_inc(x_26);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_56);
lean_ctor_set(x_11, 0, x_26);
x_57 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_58 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_57);
x_59 = l_Array_mkArray0(lean_box(0));
lean_inc(x_59);
lean_inc(x_34);
lean_inc(x_26);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_26);
lean_ctor_set(x_60, 1, x_34);
lean_ctor_set(x_60, 2, x_59);
lean_inc(x_60);
lean_inc(x_26);
x_61 = l_Lean_Syntax_node1(x_26, x_58, x_60);
lean_inc_n(x_60, 2);
lean_inc(x_26);
x_62 = l_Lean_Syntax_node5(x_26, x_55, x_11, x_61, x_60, x_60, x_60);
lean_inc(x_34);
lean_inc(x_26);
x_63 = l_Lean_Syntax_node1(x_26, x_34, x_62);
lean_inc(x_41);
lean_inc(x_26);
x_64 = l_Lean_Syntax_node1(x_26, x_41, x_63);
lean_inc(x_39);
lean_inc(x_26);
x_65 = l_Lean_Syntax_node1(x_26, x_39, x_64);
lean_inc(x_36);
lean_inc(x_26);
x_66 = l_Lean_Syntax_node2(x_26, x_36, x_15, x_65);
lean_inc(x_34);
lean_inc(x_26);
x_67 = l_Lean_Syntax_node4(x_26, x_34, x_45, x_49, x_53, x_66);
x_68 = l_Lean_Syntax_node2(x_26, x_31, x_19, x_67);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_68);
x_69 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx(x_1, x_68, x_2, x_3, x_4, x_5, x_21);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
x_73 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___lam__0(x_2, x_3, x_4, x_5, x_72);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_73, 1);
x_77 = lean_st_ref_get(x_5, x_76);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_79 = lean_ctor_get(x_77, 1);
x_80 = lean_ctor_get(x_77, 0);
lean_dec(x_80);
x_81 = lean_mk_string_unchecked("intros", 6, 6);
lean_inc(x_81);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_82 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_81);
lean_inc(x_75);
lean_ctor_set_tag(x_77, 2);
lean_ctor_set(x_77, 1, x_81);
lean_ctor_set(x_77, 0, x_75);
lean_inc(x_34);
lean_inc(x_75);
x_83 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_83, 0, x_75);
lean_ctor_set(x_83, 1, x_34);
lean_ctor_set(x_83, 2, x_59);
lean_inc(x_83);
lean_inc(x_75);
x_84 = l_Lean_Syntax_node2(x_75, x_82, x_77, x_83);
x_85 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_75);
lean_ctor_set_tag(x_73, 2);
lean_ctor_set(x_73, 1, x_85);
x_86 = lean_mk_string_unchecked("first", 5, 5);
lean_inc(x_86);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_87 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_86);
lean_inc(x_86);
lean_inc(x_75);
lean_ctor_set_tag(x_69, 2);
lean_ctor_set(x_69, 1, x_86);
lean_ctor_set(x_69, 0, x_75);
lean_inc(x_37);
lean_inc(x_75);
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_37);
lean_ctor_set(x_7, 0, x_75);
lean_inc(x_34);
lean_inc(x_75);
x_88 = l_Lean_Syntax_node1(x_75, x_34, x_9);
lean_inc(x_41);
lean_inc(x_75);
x_89 = l_Lean_Syntax_node1(x_75, x_41, x_88);
lean_inc(x_39);
lean_inc(x_75);
x_90 = l_Lean_Syntax_node1(x_75, x_39, x_89);
lean_inc(x_7);
lean_inc(x_36);
lean_inc(x_75);
x_91 = l_Lean_Syntax_node2(x_75, x_36, x_7, x_90);
lean_inc(x_34);
lean_inc(x_75);
x_92 = l_Lean_Syntax_node1(x_75, x_34, x_13);
lean_inc(x_41);
lean_inc(x_75);
x_93 = l_Lean_Syntax_node1(x_75, x_41, x_92);
lean_inc(x_39);
lean_inc(x_75);
x_94 = l_Lean_Syntax_node1(x_75, x_39, x_93);
lean_inc(x_7);
lean_inc(x_36);
lean_inc(x_75);
x_95 = l_Lean_Syntax_node2(x_75, x_36, x_7, x_94);
x_96 = lean_mk_string_unchecked("exact\?", 6, 6);
lean_inc(x_96);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_97 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_96);
lean_inc(x_75);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_75);
lean_ctor_set(x_98, 1, x_96);
lean_inc(x_75);
x_99 = l_Lean_Syntax_node2(x_75, x_97, x_98, x_83);
lean_inc(x_34);
lean_inc(x_75);
x_100 = l_Lean_Syntax_node1(x_75, x_34, x_99);
lean_inc(x_41);
lean_inc(x_75);
x_101 = l_Lean_Syntax_node1(x_75, x_41, x_100);
lean_inc(x_39);
lean_inc(x_75);
x_102 = l_Lean_Syntax_node1(x_75, x_39, x_101);
lean_inc(x_36);
lean_inc(x_75);
x_103 = l_Lean_Syntax_node2(x_75, x_36, x_7, x_102);
lean_inc(x_34);
lean_inc(x_75);
x_104 = l_Lean_Syntax_node3(x_75, x_34, x_91, x_95, x_103);
lean_inc(x_87);
lean_inc(x_75);
x_105 = l_Lean_Syntax_node2(x_75, x_87, x_69, x_104);
lean_inc(x_34);
lean_inc(x_75);
x_106 = l_Lean_Syntax_node3(x_75, x_34, x_84, x_73, x_105);
x_107 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___lam__0(x_2, x_3, x_4, x_5, x_79);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_109 = lean_ctor_get(x_107, 0);
x_110 = lean_ctor_get(x_107, 1);
x_111 = lean_st_ref_get(x_5, x_110);
lean_dec(x_5);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_113 = lean_ctor_get(x_111, 0);
lean_dec(x_113);
x_114 = lean_mk_string_unchecked("paren", 5, 5);
x_115 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_41);
lean_inc(x_75);
x_116 = l_Lean_Syntax_node1(x_75, x_41, x_106);
x_117 = lean_mk_string_unchecked(")", 1, 1);
x_118 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_114);
lean_inc(x_75);
lean_ctor_set_tag(x_107, 2);
lean_ctor_set(x_107, 1, x_115);
lean_ctor_set(x_107, 0, x_75);
lean_inc(x_39);
lean_inc(x_75);
x_119 = l_Lean_Syntax_node1(x_75, x_39, x_116);
lean_inc(x_75);
x_120 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_120, 0, x_75);
lean_ctor_set(x_120, 1, x_117);
x_121 = l_Lean_Syntax_node3(x_75, x_118, x_107, x_119, x_120);
lean_inc(x_109);
x_122 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_122, 0, x_109);
lean_ctor_set(x_122, 1, x_86);
lean_inc(x_109);
x_123 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_123, 0, x_109);
lean_ctor_set(x_123, 1, x_37);
lean_inc(x_34);
lean_inc(x_109);
x_124 = l_Lean_Syntax_node1(x_109, x_34, x_68);
lean_inc(x_41);
lean_inc(x_109);
x_125 = l_Lean_Syntax_node1(x_109, x_41, x_124);
lean_inc(x_39);
lean_inc(x_109);
x_126 = l_Lean_Syntax_node1(x_109, x_39, x_125);
lean_inc(x_123);
lean_inc(x_36);
lean_inc(x_109);
x_127 = l_Lean_Syntax_node2(x_109, x_36, x_123, x_126);
lean_inc(x_34);
lean_inc(x_109);
x_128 = l_Lean_Syntax_node1(x_109, x_34, x_71);
lean_inc(x_41);
lean_inc(x_109);
x_129 = l_Lean_Syntax_node1(x_109, x_41, x_128);
lean_inc(x_39);
lean_inc(x_109);
x_130 = l_Lean_Syntax_node1(x_109, x_39, x_129);
lean_inc(x_123);
lean_inc(x_36);
lean_inc(x_109);
x_131 = l_Lean_Syntax_node2(x_109, x_36, x_123, x_130);
lean_inc(x_34);
lean_inc(x_109);
x_132 = l_Lean_Syntax_node1(x_109, x_34, x_121);
lean_inc(x_109);
x_133 = l_Lean_Syntax_node1(x_109, x_41, x_132);
lean_inc(x_109);
x_134 = l_Lean_Syntax_node1(x_109, x_39, x_133);
lean_inc(x_109);
x_135 = l_Lean_Syntax_node2(x_109, x_36, x_123, x_134);
lean_inc(x_109);
x_136 = l_Lean_Syntax_node3(x_109, x_34, x_127, x_131, x_135);
x_137 = l_Lean_Syntax_node2(x_109, x_87, x_122, x_136);
lean_ctor_set(x_111, 0, x_137);
return x_111;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_138 = lean_ctor_get(x_111, 1);
lean_inc(x_138);
lean_dec(x_111);
x_139 = lean_mk_string_unchecked("paren", 5, 5);
x_140 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_41);
lean_inc(x_75);
x_141 = l_Lean_Syntax_node1(x_75, x_41, x_106);
x_142 = lean_mk_string_unchecked(")", 1, 1);
x_143 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_139);
lean_inc(x_75);
lean_ctor_set_tag(x_107, 2);
lean_ctor_set(x_107, 1, x_140);
lean_ctor_set(x_107, 0, x_75);
lean_inc(x_39);
lean_inc(x_75);
x_144 = l_Lean_Syntax_node1(x_75, x_39, x_141);
lean_inc(x_75);
x_145 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_145, 0, x_75);
lean_ctor_set(x_145, 1, x_142);
x_146 = l_Lean_Syntax_node3(x_75, x_143, x_107, x_144, x_145);
lean_inc(x_109);
x_147 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_147, 0, x_109);
lean_ctor_set(x_147, 1, x_86);
lean_inc(x_109);
x_148 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_148, 0, x_109);
lean_ctor_set(x_148, 1, x_37);
lean_inc(x_34);
lean_inc(x_109);
x_149 = l_Lean_Syntax_node1(x_109, x_34, x_68);
lean_inc(x_41);
lean_inc(x_109);
x_150 = l_Lean_Syntax_node1(x_109, x_41, x_149);
lean_inc(x_39);
lean_inc(x_109);
x_151 = l_Lean_Syntax_node1(x_109, x_39, x_150);
lean_inc(x_148);
lean_inc(x_36);
lean_inc(x_109);
x_152 = l_Lean_Syntax_node2(x_109, x_36, x_148, x_151);
lean_inc(x_34);
lean_inc(x_109);
x_153 = l_Lean_Syntax_node1(x_109, x_34, x_71);
lean_inc(x_41);
lean_inc(x_109);
x_154 = l_Lean_Syntax_node1(x_109, x_41, x_153);
lean_inc(x_39);
lean_inc(x_109);
x_155 = l_Lean_Syntax_node1(x_109, x_39, x_154);
lean_inc(x_148);
lean_inc(x_36);
lean_inc(x_109);
x_156 = l_Lean_Syntax_node2(x_109, x_36, x_148, x_155);
lean_inc(x_34);
lean_inc(x_109);
x_157 = l_Lean_Syntax_node1(x_109, x_34, x_146);
lean_inc(x_109);
x_158 = l_Lean_Syntax_node1(x_109, x_41, x_157);
lean_inc(x_109);
x_159 = l_Lean_Syntax_node1(x_109, x_39, x_158);
lean_inc(x_109);
x_160 = l_Lean_Syntax_node2(x_109, x_36, x_148, x_159);
lean_inc(x_109);
x_161 = l_Lean_Syntax_node3(x_109, x_34, x_152, x_156, x_160);
x_162 = l_Lean_Syntax_node2(x_109, x_87, x_147, x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_138);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_164 = lean_ctor_get(x_107, 0);
x_165 = lean_ctor_get(x_107, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_107);
x_166 = lean_st_ref_get(x_5, x_165);
lean_dec(x_5);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_168 = x_166;
} else {
 lean_dec_ref(x_166);
 x_168 = lean_box(0);
}
x_169 = lean_mk_string_unchecked("paren", 5, 5);
x_170 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_41);
lean_inc(x_75);
x_171 = l_Lean_Syntax_node1(x_75, x_41, x_106);
x_172 = lean_mk_string_unchecked(")", 1, 1);
x_173 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_169);
lean_inc(x_75);
x_174 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_174, 0, x_75);
lean_ctor_set(x_174, 1, x_170);
lean_inc(x_39);
lean_inc(x_75);
x_175 = l_Lean_Syntax_node1(x_75, x_39, x_171);
lean_inc(x_75);
x_176 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_176, 0, x_75);
lean_ctor_set(x_176, 1, x_172);
x_177 = l_Lean_Syntax_node3(x_75, x_173, x_174, x_175, x_176);
lean_inc(x_164);
x_178 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_178, 0, x_164);
lean_ctor_set(x_178, 1, x_86);
lean_inc(x_164);
x_179 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_179, 0, x_164);
lean_ctor_set(x_179, 1, x_37);
lean_inc(x_34);
lean_inc(x_164);
x_180 = l_Lean_Syntax_node1(x_164, x_34, x_68);
lean_inc(x_41);
lean_inc(x_164);
x_181 = l_Lean_Syntax_node1(x_164, x_41, x_180);
lean_inc(x_39);
lean_inc(x_164);
x_182 = l_Lean_Syntax_node1(x_164, x_39, x_181);
lean_inc(x_179);
lean_inc(x_36);
lean_inc(x_164);
x_183 = l_Lean_Syntax_node2(x_164, x_36, x_179, x_182);
lean_inc(x_34);
lean_inc(x_164);
x_184 = l_Lean_Syntax_node1(x_164, x_34, x_71);
lean_inc(x_41);
lean_inc(x_164);
x_185 = l_Lean_Syntax_node1(x_164, x_41, x_184);
lean_inc(x_39);
lean_inc(x_164);
x_186 = l_Lean_Syntax_node1(x_164, x_39, x_185);
lean_inc(x_179);
lean_inc(x_36);
lean_inc(x_164);
x_187 = l_Lean_Syntax_node2(x_164, x_36, x_179, x_186);
lean_inc(x_34);
lean_inc(x_164);
x_188 = l_Lean_Syntax_node1(x_164, x_34, x_177);
lean_inc(x_164);
x_189 = l_Lean_Syntax_node1(x_164, x_41, x_188);
lean_inc(x_164);
x_190 = l_Lean_Syntax_node1(x_164, x_39, x_189);
lean_inc(x_164);
x_191 = l_Lean_Syntax_node2(x_164, x_36, x_179, x_190);
lean_inc(x_164);
x_192 = l_Lean_Syntax_node3(x_164, x_34, x_183, x_187, x_191);
x_193 = l_Lean_Syntax_node2(x_164, x_87, x_178, x_192);
if (lean_is_scalar(x_168)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_168;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_167);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_195 = lean_ctor_get(x_77, 1);
lean_inc(x_195);
lean_dec(x_77);
x_196 = lean_mk_string_unchecked("intros", 6, 6);
lean_inc(x_196);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_197 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_196);
lean_inc(x_75);
x_198 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_198, 0, x_75);
lean_ctor_set(x_198, 1, x_196);
lean_inc(x_34);
lean_inc(x_75);
x_199 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_199, 0, x_75);
lean_ctor_set(x_199, 1, x_34);
lean_ctor_set(x_199, 2, x_59);
lean_inc(x_199);
lean_inc(x_75);
x_200 = l_Lean_Syntax_node2(x_75, x_197, x_198, x_199);
x_201 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_75);
lean_ctor_set_tag(x_73, 2);
lean_ctor_set(x_73, 1, x_201);
x_202 = lean_mk_string_unchecked("first", 5, 5);
lean_inc(x_202);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_203 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_202);
lean_inc(x_202);
lean_inc(x_75);
lean_ctor_set_tag(x_69, 2);
lean_ctor_set(x_69, 1, x_202);
lean_ctor_set(x_69, 0, x_75);
lean_inc(x_37);
lean_inc(x_75);
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_37);
lean_ctor_set(x_7, 0, x_75);
lean_inc(x_34);
lean_inc(x_75);
x_204 = l_Lean_Syntax_node1(x_75, x_34, x_9);
lean_inc(x_41);
lean_inc(x_75);
x_205 = l_Lean_Syntax_node1(x_75, x_41, x_204);
lean_inc(x_39);
lean_inc(x_75);
x_206 = l_Lean_Syntax_node1(x_75, x_39, x_205);
lean_inc(x_7);
lean_inc(x_36);
lean_inc(x_75);
x_207 = l_Lean_Syntax_node2(x_75, x_36, x_7, x_206);
lean_inc(x_34);
lean_inc(x_75);
x_208 = l_Lean_Syntax_node1(x_75, x_34, x_13);
lean_inc(x_41);
lean_inc(x_75);
x_209 = l_Lean_Syntax_node1(x_75, x_41, x_208);
lean_inc(x_39);
lean_inc(x_75);
x_210 = l_Lean_Syntax_node1(x_75, x_39, x_209);
lean_inc(x_7);
lean_inc(x_36);
lean_inc(x_75);
x_211 = l_Lean_Syntax_node2(x_75, x_36, x_7, x_210);
x_212 = lean_mk_string_unchecked("exact\?", 6, 6);
lean_inc(x_212);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_213 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_212);
lean_inc(x_75);
x_214 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_214, 0, x_75);
lean_ctor_set(x_214, 1, x_212);
lean_inc(x_75);
x_215 = l_Lean_Syntax_node2(x_75, x_213, x_214, x_199);
lean_inc(x_34);
lean_inc(x_75);
x_216 = l_Lean_Syntax_node1(x_75, x_34, x_215);
lean_inc(x_41);
lean_inc(x_75);
x_217 = l_Lean_Syntax_node1(x_75, x_41, x_216);
lean_inc(x_39);
lean_inc(x_75);
x_218 = l_Lean_Syntax_node1(x_75, x_39, x_217);
lean_inc(x_36);
lean_inc(x_75);
x_219 = l_Lean_Syntax_node2(x_75, x_36, x_7, x_218);
lean_inc(x_34);
lean_inc(x_75);
x_220 = l_Lean_Syntax_node3(x_75, x_34, x_207, x_211, x_219);
lean_inc(x_203);
lean_inc(x_75);
x_221 = l_Lean_Syntax_node2(x_75, x_203, x_69, x_220);
lean_inc(x_34);
lean_inc(x_75);
x_222 = l_Lean_Syntax_node3(x_75, x_34, x_200, x_73, x_221);
x_223 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___lam__0(x_2, x_3, x_4, x_5, x_195);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_227 = lean_st_ref_get(x_5, x_225);
lean_dec(x_5);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_229 = x_227;
} else {
 lean_dec_ref(x_227);
 x_229 = lean_box(0);
}
x_230 = lean_mk_string_unchecked("paren", 5, 5);
x_231 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_41);
lean_inc(x_75);
x_232 = l_Lean_Syntax_node1(x_75, x_41, x_222);
x_233 = lean_mk_string_unchecked(")", 1, 1);
x_234 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_230);
lean_inc(x_75);
if (lean_is_scalar(x_226)) {
 x_235 = lean_alloc_ctor(2, 2, 0);
} else {
 x_235 = x_226;
 lean_ctor_set_tag(x_235, 2);
}
lean_ctor_set(x_235, 0, x_75);
lean_ctor_set(x_235, 1, x_231);
lean_inc(x_39);
lean_inc(x_75);
x_236 = l_Lean_Syntax_node1(x_75, x_39, x_232);
lean_inc(x_75);
x_237 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_237, 0, x_75);
lean_ctor_set(x_237, 1, x_233);
x_238 = l_Lean_Syntax_node3(x_75, x_234, x_235, x_236, x_237);
lean_inc(x_224);
x_239 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_239, 0, x_224);
lean_ctor_set(x_239, 1, x_202);
lean_inc(x_224);
x_240 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_240, 0, x_224);
lean_ctor_set(x_240, 1, x_37);
lean_inc(x_34);
lean_inc(x_224);
x_241 = l_Lean_Syntax_node1(x_224, x_34, x_68);
lean_inc(x_41);
lean_inc(x_224);
x_242 = l_Lean_Syntax_node1(x_224, x_41, x_241);
lean_inc(x_39);
lean_inc(x_224);
x_243 = l_Lean_Syntax_node1(x_224, x_39, x_242);
lean_inc(x_240);
lean_inc(x_36);
lean_inc(x_224);
x_244 = l_Lean_Syntax_node2(x_224, x_36, x_240, x_243);
lean_inc(x_34);
lean_inc(x_224);
x_245 = l_Lean_Syntax_node1(x_224, x_34, x_71);
lean_inc(x_41);
lean_inc(x_224);
x_246 = l_Lean_Syntax_node1(x_224, x_41, x_245);
lean_inc(x_39);
lean_inc(x_224);
x_247 = l_Lean_Syntax_node1(x_224, x_39, x_246);
lean_inc(x_240);
lean_inc(x_36);
lean_inc(x_224);
x_248 = l_Lean_Syntax_node2(x_224, x_36, x_240, x_247);
lean_inc(x_34);
lean_inc(x_224);
x_249 = l_Lean_Syntax_node1(x_224, x_34, x_238);
lean_inc(x_224);
x_250 = l_Lean_Syntax_node1(x_224, x_41, x_249);
lean_inc(x_224);
x_251 = l_Lean_Syntax_node1(x_224, x_39, x_250);
lean_inc(x_224);
x_252 = l_Lean_Syntax_node2(x_224, x_36, x_240, x_251);
lean_inc(x_224);
x_253 = l_Lean_Syntax_node3(x_224, x_34, x_244, x_248, x_252);
x_254 = l_Lean_Syntax_node2(x_224, x_203, x_239, x_253);
if (lean_is_scalar(x_229)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_229;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_228);
return x_255;
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_256 = lean_ctor_get(x_73, 0);
x_257 = lean_ctor_get(x_73, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_73);
x_258 = lean_st_ref_get(x_5, x_257);
x_259 = lean_ctor_get(x_258, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_260 = x_258;
} else {
 lean_dec_ref(x_258);
 x_260 = lean_box(0);
}
x_261 = lean_mk_string_unchecked("intros", 6, 6);
lean_inc(x_261);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_262 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_261);
lean_inc(x_256);
if (lean_is_scalar(x_260)) {
 x_263 = lean_alloc_ctor(2, 2, 0);
} else {
 x_263 = x_260;
 lean_ctor_set_tag(x_263, 2);
}
lean_ctor_set(x_263, 0, x_256);
lean_ctor_set(x_263, 1, x_261);
lean_inc(x_34);
lean_inc(x_256);
x_264 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_264, 0, x_256);
lean_ctor_set(x_264, 1, x_34);
lean_ctor_set(x_264, 2, x_59);
lean_inc(x_264);
lean_inc(x_256);
x_265 = l_Lean_Syntax_node2(x_256, x_262, x_263, x_264);
x_266 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_256);
x_267 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_267, 0, x_256);
lean_ctor_set(x_267, 1, x_266);
x_268 = lean_mk_string_unchecked("first", 5, 5);
lean_inc(x_268);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_269 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_268);
lean_inc(x_268);
lean_inc(x_256);
lean_ctor_set_tag(x_69, 2);
lean_ctor_set(x_69, 1, x_268);
lean_ctor_set(x_69, 0, x_256);
lean_inc(x_37);
lean_inc(x_256);
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_37);
lean_ctor_set(x_7, 0, x_256);
lean_inc(x_34);
lean_inc(x_256);
x_270 = l_Lean_Syntax_node1(x_256, x_34, x_9);
lean_inc(x_41);
lean_inc(x_256);
x_271 = l_Lean_Syntax_node1(x_256, x_41, x_270);
lean_inc(x_39);
lean_inc(x_256);
x_272 = l_Lean_Syntax_node1(x_256, x_39, x_271);
lean_inc(x_7);
lean_inc(x_36);
lean_inc(x_256);
x_273 = l_Lean_Syntax_node2(x_256, x_36, x_7, x_272);
lean_inc(x_34);
lean_inc(x_256);
x_274 = l_Lean_Syntax_node1(x_256, x_34, x_13);
lean_inc(x_41);
lean_inc(x_256);
x_275 = l_Lean_Syntax_node1(x_256, x_41, x_274);
lean_inc(x_39);
lean_inc(x_256);
x_276 = l_Lean_Syntax_node1(x_256, x_39, x_275);
lean_inc(x_7);
lean_inc(x_36);
lean_inc(x_256);
x_277 = l_Lean_Syntax_node2(x_256, x_36, x_7, x_276);
x_278 = lean_mk_string_unchecked("exact\?", 6, 6);
lean_inc(x_278);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_279 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_278);
lean_inc(x_256);
x_280 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_280, 0, x_256);
lean_ctor_set(x_280, 1, x_278);
lean_inc(x_256);
x_281 = l_Lean_Syntax_node2(x_256, x_279, x_280, x_264);
lean_inc(x_34);
lean_inc(x_256);
x_282 = l_Lean_Syntax_node1(x_256, x_34, x_281);
lean_inc(x_41);
lean_inc(x_256);
x_283 = l_Lean_Syntax_node1(x_256, x_41, x_282);
lean_inc(x_39);
lean_inc(x_256);
x_284 = l_Lean_Syntax_node1(x_256, x_39, x_283);
lean_inc(x_36);
lean_inc(x_256);
x_285 = l_Lean_Syntax_node2(x_256, x_36, x_7, x_284);
lean_inc(x_34);
lean_inc(x_256);
x_286 = l_Lean_Syntax_node3(x_256, x_34, x_273, x_277, x_285);
lean_inc(x_269);
lean_inc(x_256);
x_287 = l_Lean_Syntax_node2(x_256, x_269, x_69, x_286);
lean_inc(x_34);
lean_inc(x_256);
x_288 = l_Lean_Syntax_node3(x_256, x_34, x_265, x_267, x_287);
x_289 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___lam__0(x_2, x_3, x_4, x_5, x_259);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_292 = x_289;
} else {
 lean_dec_ref(x_289);
 x_292 = lean_box(0);
}
x_293 = lean_st_ref_get(x_5, x_291);
lean_dec(x_5);
x_294 = lean_ctor_get(x_293, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_295 = x_293;
} else {
 lean_dec_ref(x_293);
 x_295 = lean_box(0);
}
x_296 = lean_mk_string_unchecked("paren", 5, 5);
x_297 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_41);
lean_inc(x_256);
x_298 = l_Lean_Syntax_node1(x_256, x_41, x_288);
x_299 = lean_mk_string_unchecked(")", 1, 1);
x_300 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_296);
lean_inc(x_256);
if (lean_is_scalar(x_292)) {
 x_301 = lean_alloc_ctor(2, 2, 0);
} else {
 x_301 = x_292;
 lean_ctor_set_tag(x_301, 2);
}
lean_ctor_set(x_301, 0, x_256);
lean_ctor_set(x_301, 1, x_297);
lean_inc(x_39);
lean_inc(x_256);
x_302 = l_Lean_Syntax_node1(x_256, x_39, x_298);
lean_inc(x_256);
x_303 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_303, 0, x_256);
lean_ctor_set(x_303, 1, x_299);
x_304 = l_Lean_Syntax_node3(x_256, x_300, x_301, x_302, x_303);
lean_inc(x_290);
x_305 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_305, 0, x_290);
lean_ctor_set(x_305, 1, x_268);
lean_inc(x_290);
x_306 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_306, 0, x_290);
lean_ctor_set(x_306, 1, x_37);
lean_inc(x_34);
lean_inc(x_290);
x_307 = l_Lean_Syntax_node1(x_290, x_34, x_68);
lean_inc(x_41);
lean_inc(x_290);
x_308 = l_Lean_Syntax_node1(x_290, x_41, x_307);
lean_inc(x_39);
lean_inc(x_290);
x_309 = l_Lean_Syntax_node1(x_290, x_39, x_308);
lean_inc(x_306);
lean_inc(x_36);
lean_inc(x_290);
x_310 = l_Lean_Syntax_node2(x_290, x_36, x_306, x_309);
lean_inc(x_34);
lean_inc(x_290);
x_311 = l_Lean_Syntax_node1(x_290, x_34, x_71);
lean_inc(x_41);
lean_inc(x_290);
x_312 = l_Lean_Syntax_node1(x_290, x_41, x_311);
lean_inc(x_39);
lean_inc(x_290);
x_313 = l_Lean_Syntax_node1(x_290, x_39, x_312);
lean_inc(x_306);
lean_inc(x_36);
lean_inc(x_290);
x_314 = l_Lean_Syntax_node2(x_290, x_36, x_306, x_313);
lean_inc(x_34);
lean_inc(x_290);
x_315 = l_Lean_Syntax_node1(x_290, x_34, x_304);
lean_inc(x_290);
x_316 = l_Lean_Syntax_node1(x_290, x_41, x_315);
lean_inc(x_290);
x_317 = l_Lean_Syntax_node1(x_290, x_39, x_316);
lean_inc(x_290);
x_318 = l_Lean_Syntax_node2(x_290, x_36, x_306, x_317);
lean_inc(x_290);
x_319 = l_Lean_Syntax_node3(x_290, x_34, x_310, x_314, x_318);
x_320 = l_Lean_Syntax_node2(x_290, x_269, x_305, x_319);
if (lean_is_scalar(x_295)) {
 x_321 = lean_alloc_ctor(0, 2, 0);
} else {
 x_321 = x_295;
}
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_294);
return x_321;
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_322 = lean_ctor_get(x_69, 0);
x_323 = lean_ctor_get(x_69, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_69);
x_324 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___lam__0(x_2, x_3, x_4, x_5, x_323);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_327 = x_324;
} else {
 lean_dec_ref(x_324);
 x_327 = lean_box(0);
}
x_328 = lean_st_ref_get(x_5, x_326);
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_330 = x_328;
} else {
 lean_dec_ref(x_328);
 x_330 = lean_box(0);
}
x_331 = lean_mk_string_unchecked("intros", 6, 6);
lean_inc(x_331);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_332 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_331);
lean_inc(x_325);
if (lean_is_scalar(x_330)) {
 x_333 = lean_alloc_ctor(2, 2, 0);
} else {
 x_333 = x_330;
 lean_ctor_set_tag(x_333, 2);
}
lean_ctor_set(x_333, 0, x_325);
lean_ctor_set(x_333, 1, x_331);
lean_inc(x_34);
lean_inc(x_325);
x_334 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_334, 0, x_325);
lean_ctor_set(x_334, 1, x_34);
lean_ctor_set(x_334, 2, x_59);
lean_inc(x_334);
lean_inc(x_325);
x_335 = l_Lean_Syntax_node2(x_325, x_332, x_333, x_334);
x_336 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_325);
if (lean_is_scalar(x_327)) {
 x_337 = lean_alloc_ctor(2, 2, 0);
} else {
 x_337 = x_327;
 lean_ctor_set_tag(x_337, 2);
}
lean_ctor_set(x_337, 0, x_325);
lean_ctor_set(x_337, 1, x_336);
x_338 = lean_mk_string_unchecked("first", 5, 5);
lean_inc(x_338);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_339 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_338);
lean_inc(x_338);
lean_inc(x_325);
x_340 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_340, 0, x_325);
lean_ctor_set(x_340, 1, x_338);
lean_inc(x_37);
lean_inc(x_325);
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_37);
lean_ctor_set(x_7, 0, x_325);
lean_inc(x_34);
lean_inc(x_325);
x_341 = l_Lean_Syntax_node1(x_325, x_34, x_9);
lean_inc(x_41);
lean_inc(x_325);
x_342 = l_Lean_Syntax_node1(x_325, x_41, x_341);
lean_inc(x_39);
lean_inc(x_325);
x_343 = l_Lean_Syntax_node1(x_325, x_39, x_342);
lean_inc(x_7);
lean_inc(x_36);
lean_inc(x_325);
x_344 = l_Lean_Syntax_node2(x_325, x_36, x_7, x_343);
lean_inc(x_34);
lean_inc(x_325);
x_345 = l_Lean_Syntax_node1(x_325, x_34, x_13);
lean_inc(x_41);
lean_inc(x_325);
x_346 = l_Lean_Syntax_node1(x_325, x_41, x_345);
lean_inc(x_39);
lean_inc(x_325);
x_347 = l_Lean_Syntax_node1(x_325, x_39, x_346);
lean_inc(x_7);
lean_inc(x_36);
lean_inc(x_325);
x_348 = l_Lean_Syntax_node2(x_325, x_36, x_7, x_347);
x_349 = lean_mk_string_unchecked("exact\?", 6, 6);
lean_inc(x_349);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_350 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_349);
lean_inc(x_325);
x_351 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_351, 0, x_325);
lean_ctor_set(x_351, 1, x_349);
lean_inc(x_325);
x_352 = l_Lean_Syntax_node2(x_325, x_350, x_351, x_334);
lean_inc(x_34);
lean_inc(x_325);
x_353 = l_Lean_Syntax_node1(x_325, x_34, x_352);
lean_inc(x_41);
lean_inc(x_325);
x_354 = l_Lean_Syntax_node1(x_325, x_41, x_353);
lean_inc(x_39);
lean_inc(x_325);
x_355 = l_Lean_Syntax_node1(x_325, x_39, x_354);
lean_inc(x_36);
lean_inc(x_325);
x_356 = l_Lean_Syntax_node2(x_325, x_36, x_7, x_355);
lean_inc(x_34);
lean_inc(x_325);
x_357 = l_Lean_Syntax_node3(x_325, x_34, x_344, x_348, x_356);
lean_inc(x_339);
lean_inc(x_325);
x_358 = l_Lean_Syntax_node2(x_325, x_339, x_340, x_357);
lean_inc(x_34);
lean_inc(x_325);
x_359 = l_Lean_Syntax_node3(x_325, x_34, x_335, x_337, x_358);
x_360 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___lam__0(x_2, x_3, x_4, x_5, x_329);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_363 = x_360;
} else {
 lean_dec_ref(x_360);
 x_363 = lean_box(0);
}
x_364 = lean_st_ref_get(x_5, x_362);
lean_dec(x_5);
x_365 = lean_ctor_get(x_364, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_366 = x_364;
} else {
 lean_dec_ref(x_364);
 x_366 = lean_box(0);
}
x_367 = lean_mk_string_unchecked("paren", 5, 5);
x_368 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_41);
lean_inc(x_325);
x_369 = l_Lean_Syntax_node1(x_325, x_41, x_359);
x_370 = lean_mk_string_unchecked(")", 1, 1);
x_371 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_367);
lean_inc(x_325);
if (lean_is_scalar(x_363)) {
 x_372 = lean_alloc_ctor(2, 2, 0);
} else {
 x_372 = x_363;
 lean_ctor_set_tag(x_372, 2);
}
lean_ctor_set(x_372, 0, x_325);
lean_ctor_set(x_372, 1, x_368);
lean_inc(x_39);
lean_inc(x_325);
x_373 = l_Lean_Syntax_node1(x_325, x_39, x_369);
lean_inc(x_325);
x_374 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_374, 0, x_325);
lean_ctor_set(x_374, 1, x_370);
x_375 = l_Lean_Syntax_node3(x_325, x_371, x_372, x_373, x_374);
lean_inc(x_361);
x_376 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_376, 0, x_361);
lean_ctor_set(x_376, 1, x_338);
lean_inc(x_361);
x_377 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_377, 0, x_361);
lean_ctor_set(x_377, 1, x_37);
lean_inc(x_34);
lean_inc(x_361);
x_378 = l_Lean_Syntax_node1(x_361, x_34, x_68);
lean_inc(x_41);
lean_inc(x_361);
x_379 = l_Lean_Syntax_node1(x_361, x_41, x_378);
lean_inc(x_39);
lean_inc(x_361);
x_380 = l_Lean_Syntax_node1(x_361, x_39, x_379);
lean_inc(x_377);
lean_inc(x_36);
lean_inc(x_361);
x_381 = l_Lean_Syntax_node2(x_361, x_36, x_377, x_380);
lean_inc(x_34);
lean_inc(x_361);
x_382 = l_Lean_Syntax_node1(x_361, x_34, x_322);
lean_inc(x_41);
lean_inc(x_361);
x_383 = l_Lean_Syntax_node1(x_361, x_41, x_382);
lean_inc(x_39);
lean_inc(x_361);
x_384 = l_Lean_Syntax_node1(x_361, x_39, x_383);
lean_inc(x_377);
lean_inc(x_36);
lean_inc(x_361);
x_385 = l_Lean_Syntax_node2(x_361, x_36, x_377, x_384);
lean_inc(x_34);
lean_inc(x_361);
x_386 = l_Lean_Syntax_node1(x_361, x_34, x_375);
lean_inc(x_361);
x_387 = l_Lean_Syntax_node1(x_361, x_41, x_386);
lean_inc(x_361);
x_388 = l_Lean_Syntax_node1(x_361, x_39, x_387);
lean_inc(x_361);
x_389 = l_Lean_Syntax_node2(x_361, x_36, x_377, x_388);
lean_inc(x_361);
x_390 = l_Lean_Syntax_node3(x_361, x_34, x_381, x_385, x_389);
x_391 = l_Lean_Syntax_node2(x_361, x_339, x_376, x_390);
if (lean_is_scalar(x_366)) {
 x_392 = lean_alloc_ctor(0, 2, 0);
} else {
 x_392 = x_366;
}
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_365);
return x_392;
}
}
else
{
lean_dec(x_68);
lean_dec(x_59);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_13);
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_69;
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_393 = lean_ctor_get(x_19, 1);
lean_inc(x_393);
lean_dec(x_19);
x_394 = lean_ctor_get(x_4, 5);
lean_inc(x_394);
x_395 = lean_box(0);
x_396 = lean_unbox(x_395);
x_397 = l_Lean_SourceInfo_fromRef(x_394, x_396);
lean_dec(x_394);
x_398 = lean_mk_string_unchecked("Lean", 4, 4);
x_399 = lean_mk_string_unchecked("Parser", 6, 6);
x_400 = lean_mk_string_unchecked("Tactic", 6, 6);
x_401 = lean_mk_string_unchecked("attemptAll", 10, 10);
lean_inc(x_400);
lean_inc(x_399);
lean_inc(x_398);
x_402 = l_Lean_Name_mkStr4(x_398, x_399, x_400, x_401);
x_403 = lean_mk_string_unchecked("attempt_all", 11, 11);
lean_inc(x_397);
x_404 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_404, 0, x_397);
lean_ctor_set(x_404, 1, x_403);
x_405 = lean_mk_string_unchecked("null", 4, 4);
x_406 = l_Lean_Name_mkStr1(x_405);
x_407 = lean_mk_string_unchecked("group", 5, 5);
x_408 = l_Lean_Name_mkStr1(x_407);
x_409 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_409);
lean_inc(x_397);
lean_ctor_set_tag(x_15, 2);
lean_ctor_set(x_15, 1, x_409);
lean_ctor_set(x_15, 0, x_397);
x_410 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_400);
lean_inc(x_399);
lean_inc(x_398);
x_411 = l_Lean_Name_mkStr4(x_398, x_399, x_400, x_410);
x_412 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_400);
lean_inc(x_399);
lean_inc(x_398);
x_413 = l_Lean_Name_mkStr4(x_398, x_399, x_400, x_412);
lean_inc(x_9);
lean_inc(x_406);
lean_inc(x_397);
x_414 = l_Lean_Syntax_node1(x_397, x_406, x_9);
lean_inc(x_413);
lean_inc(x_397);
x_415 = l_Lean_Syntax_node1(x_397, x_413, x_414);
lean_inc(x_411);
lean_inc(x_397);
x_416 = l_Lean_Syntax_node1(x_397, x_411, x_415);
lean_inc(x_15);
lean_inc(x_408);
lean_inc(x_397);
x_417 = l_Lean_Syntax_node2(x_397, x_408, x_15, x_416);
lean_inc(x_13);
lean_inc(x_406);
lean_inc(x_397);
x_418 = l_Lean_Syntax_node1(x_397, x_406, x_13);
lean_inc(x_413);
lean_inc(x_397);
x_419 = l_Lean_Syntax_node1(x_397, x_413, x_418);
lean_inc(x_411);
lean_inc(x_397);
x_420 = l_Lean_Syntax_node1(x_397, x_411, x_419);
lean_inc(x_15);
lean_inc(x_408);
lean_inc(x_397);
x_421 = l_Lean_Syntax_node2(x_397, x_408, x_15, x_420);
lean_inc(x_406);
lean_inc(x_397);
x_422 = l_Lean_Syntax_node1(x_397, x_406, x_17);
lean_inc(x_413);
lean_inc(x_397);
x_423 = l_Lean_Syntax_node1(x_397, x_413, x_422);
lean_inc(x_411);
lean_inc(x_397);
x_424 = l_Lean_Syntax_node1(x_397, x_411, x_423);
lean_inc(x_15);
lean_inc(x_408);
lean_inc(x_397);
x_425 = l_Lean_Syntax_node2(x_397, x_408, x_15, x_424);
x_426 = lean_mk_string_unchecked("simpAll", 7, 7);
lean_inc(x_400);
lean_inc(x_399);
lean_inc(x_398);
x_427 = l_Lean_Name_mkStr4(x_398, x_399, x_400, x_426);
x_428 = lean_mk_string_unchecked("simp_all", 8, 8);
lean_inc(x_397);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_428);
lean_ctor_set(x_11, 0, x_397);
x_429 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_400);
lean_inc(x_399);
lean_inc(x_398);
x_430 = l_Lean_Name_mkStr4(x_398, x_399, x_400, x_429);
x_431 = l_Array_mkArray0(lean_box(0));
lean_inc(x_431);
lean_inc(x_406);
lean_inc(x_397);
x_432 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_432, 0, x_397);
lean_ctor_set(x_432, 1, x_406);
lean_ctor_set(x_432, 2, x_431);
lean_inc(x_432);
lean_inc(x_397);
x_433 = l_Lean_Syntax_node1(x_397, x_430, x_432);
lean_inc_n(x_432, 2);
lean_inc(x_397);
x_434 = l_Lean_Syntax_node5(x_397, x_427, x_11, x_433, x_432, x_432, x_432);
lean_inc(x_406);
lean_inc(x_397);
x_435 = l_Lean_Syntax_node1(x_397, x_406, x_434);
lean_inc(x_413);
lean_inc(x_397);
x_436 = l_Lean_Syntax_node1(x_397, x_413, x_435);
lean_inc(x_411);
lean_inc(x_397);
x_437 = l_Lean_Syntax_node1(x_397, x_411, x_436);
lean_inc(x_408);
lean_inc(x_397);
x_438 = l_Lean_Syntax_node2(x_397, x_408, x_15, x_437);
lean_inc(x_406);
lean_inc(x_397);
x_439 = l_Lean_Syntax_node4(x_397, x_406, x_417, x_421, x_425, x_438);
x_440 = l_Lean_Syntax_node2(x_397, x_402, x_404, x_439);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_440);
x_441 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx(x_1, x_440, x_2, x_3, x_4, x_5, x_393);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_442 = lean_ctor_get(x_441, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_441, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 x_444 = x_441;
} else {
 lean_dec_ref(x_441);
 x_444 = lean_box(0);
}
x_445 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___lam__0(x_2, x_3, x_4, x_5, x_443);
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_448 = x_445;
} else {
 lean_dec_ref(x_445);
 x_448 = lean_box(0);
}
x_449 = lean_st_ref_get(x_5, x_447);
x_450 = lean_ctor_get(x_449, 1);
lean_inc(x_450);
if (lean_is_exclusive(x_449)) {
 lean_ctor_release(x_449, 0);
 lean_ctor_release(x_449, 1);
 x_451 = x_449;
} else {
 lean_dec_ref(x_449);
 x_451 = lean_box(0);
}
x_452 = lean_mk_string_unchecked("intros", 6, 6);
lean_inc(x_452);
lean_inc(x_400);
lean_inc(x_399);
lean_inc(x_398);
x_453 = l_Lean_Name_mkStr4(x_398, x_399, x_400, x_452);
lean_inc(x_446);
if (lean_is_scalar(x_451)) {
 x_454 = lean_alloc_ctor(2, 2, 0);
} else {
 x_454 = x_451;
 lean_ctor_set_tag(x_454, 2);
}
lean_ctor_set(x_454, 0, x_446);
lean_ctor_set(x_454, 1, x_452);
lean_inc(x_406);
lean_inc(x_446);
x_455 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_455, 0, x_446);
lean_ctor_set(x_455, 1, x_406);
lean_ctor_set(x_455, 2, x_431);
lean_inc(x_455);
lean_inc(x_446);
x_456 = l_Lean_Syntax_node2(x_446, x_453, x_454, x_455);
x_457 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_446);
if (lean_is_scalar(x_448)) {
 x_458 = lean_alloc_ctor(2, 2, 0);
} else {
 x_458 = x_448;
 lean_ctor_set_tag(x_458, 2);
}
lean_ctor_set(x_458, 0, x_446);
lean_ctor_set(x_458, 1, x_457);
x_459 = lean_mk_string_unchecked("first", 5, 5);
lean_inc(x_459);
lean_inc(x_400);
lean_inc(x_399);
lean_inc(x_398);
x_460 = l_Lean_Name_mkStr4(x_398, x_399, x_400, x_459);
lean_inc(x_459);
lean_inc(x_446);
if (lean_is_scalar(x_444)) {
 x_461 = lean_alloc_ctor(2, 2, 0);
} else {
 x_461 = x_444;
 lean_ctor_set_tag(x_461, 2);
}
lean_ctor_set(x_461, 0, x_446);
lean_ctor_set(x_461, 1, x_459);
lean_inc(x_409);
lean_inc(x_446);
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_409);
lean_ctor_set(x_7, 0, x_446);
lean_inc(x_406);
lean_inc(x_446);
x_462 = l_Lean_Syntax_node1(x_446, x_406, x_9);
lean_inc(x_413);
lean_inc(x_446);
x_463 = l_Lean_Syntax_node1(x_446, x_413, x_462);
lean_inc(x_411);
lean_inc(x_446);
x_464 = l_Lean_Syntax_node1(x_446, x_411, x_463);
lean_inc(x_7);
lean_inc(x_408);
lean_inc(x_446);
x_465 = l_Lean_Syntax_node2(x_446, x_408, x_7, x_464);
lean_inc(x_406);
lean_inc(x_446);
x_466 = l_Lean_Syntax_node1(x_446, x_406, x_13);
lean_inc(x_413);
lean_inc(x_446);
x_467 = l_Lean_Syntax_node1(x_446, x_413, x_466);
lean_inc(x_411);
lean_inc(x_446);
x_468 = l_Lean_Syntax_node1(x_446, x_411, x_467);
lean_inc(x_7);
lean_inc(x_408);
lean_inc(x_446);
x_469 = l_Lean_Syntax_node2(x_446, x_408, x_7, x_468);
x_470 = lean_mk_string_unchecked("exact\?", 6, 6);
lean_inc(x_470);
lean_inc(x_400);
lean_inc(x_399);
lean_inc(x_398);
x_471 = l_Lean_Name_mkStr4(x_398, x_399, x_400, x_470);
lean_inc(x_446);
x_472 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_472, 0, x_446);
lean_ctor_set(x_472, 1, x_470);
lean_inc(x_446);
x_473 = l_Lean_Syntax_node2(x_446, x_471, x_472, x_455);
lean_inc(x_406);
lean_inc(x_446);
x_474 = l_Lean_Syntax_node1(x_446, x_406, x_473);
lean_inc(x_413);
lean_inc(x_446);
x_475 = l_Lean_Syntax_node1(x_446, x_413, x_474);
lean_inc(x_411);
lean_inc(x_446);
x_476 = l_Lean_Syntax_node1(x_446, x_411, x_475);
lean_inc(x_408);
lean_inc(x_446);
x_477 = l_Lean_Syntax_node2(x_446, x_408, x_7, x_476);
lean_inc(x_406);
lean_inc(x_446);
x_478 = l_Lean_Syntax_node3(x_446, x_406, x_465, x_469, x_477);
lean_inc(x_460);
lean_inc(x_446);
x_479 = l_Lean_Syntax_node2(x_446, x_460, x_461, x_478);
lean_inc(x_406);
lean_inc(x_446);
x_480 = l_Lean_Syntax_node3(x_446, x_406, x_456, x_458, x_479);
x_481 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___lam__0(x_2, x_3, x_4, x_5, x_450);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_481, 1);
lean_inc(x_483);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 x_484 = x_481;
} else {
 lean_dec_ref(x_481);
 x_484 = lean_box(0);
}
x_485 = lean_st_ref_get(x_5, x_483);
lean_dec(x_5);
x_486 = lean_ctor_get(x_485, 1);
lean_inc(x_486);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 lean_ctor_release(x_485, 1);
 x_487 = x_485;
} else {
 lean_dec_ref(x_485);
 x_487 = lean_box(0);
}
x_488 = lean_mk_string_unchecked("paren", 5, 5);
x_489 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_413);
lean_inc(x_446);
x_490 = l_Lean_Syntax_node1(x_446, x_413, x_480);
x_491 = lean_mk_string_unchecked(")", 1, 1);
x_492 = l_Lean_Name_mkStr4(x_398, x_399, x_400, x_488);
lean_inc(x_446);
if (lean_is_scalar(x_484)) {
 x_493 = lean_alloc_ctor(2, 2, 0);
} else {
 x_493 = x_484;
 lean_ctor_set_tag(x_493, 2);
}
lean_ctor_set(x_493, 0, x_446);
lean_ctor_set(x_493, 1, x_489);
lean_inc(x_411);
lean_inc(x_446);
x_494 = l_Lean_Syntax_node1(x_446, x_411, x_490);
lean_inc(x_446);
x_495 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_495, 0, x_446);
lean_ctor_set(x_495, 1, x_491);
x_496 = l_Lean_Syntax_node3(x_446, x_492, x_493, x_494, x_495);
lean_inc(x_482);
x_497 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_497, 0, x_482);
lean_ctor_set(x_497, 1, x_459);
lean_inc(x_482);
x_498 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_498, 0, x_482);
lean_ctor_set(x_498, 1, x_409);
lean_inc(x_406);
lean_inc(x_482);
x_499 = l_Lean_Syntax_node1(x_482, x_406, x_440);
lean_inc(x_413);
lean_inc(x_482);
x_500 = l_Lean_Syntax_node1(x_482, x_413, x_499);
lean_inc(x_411);
lean_inc(x_482);
x_501 = l_Lean_Syntax_node1(x_482, x_411, x_500);
lean_inc(x_498);
lean_inc(x_408);
lean_inc(x_482);
x_502 = l_Lean_Syntax_node2(x_482, x_408, x_498, x_501);
lean_inc(x_406);
lean_inc(x_482);
x_503 = l_Lean_Syntax_node1(x_482, x_406, x_442);
lean_inc(x_413);
lean_inc(x_482);
x_504 = l_Lean_Syntax_node1(x_482, x_413, x_503);
lean_inc(x_411);
lean_inc(x_482);
x_505 = l_Lean_Syntax_node1(x_482, x_411, x_504);
lean_inc(x_498);
lean_inc(x_408);
lean_inc(x_482);
x_506 = l_Lean_Syntax_node2(x_482, x_408, x_498, x_505);
lean_inc(x_406);
lean_inc(x_482);
x_507 = l_Lean_Syntax_node1(x_482, x_406, x_496);
lean_inc(x_482);
x_508 = l_Lean_Syntax_node1(x_482, x_413, x_507);
lean_inc(x_482);
x_509 = l_Lean_Syntax_node1(x_482, x_411, x_508);
lean_inc(x_482);
x_510 = l_Lean_Syntax_node2(x_482, x_408, x_498, x_509);
lean_inc(x_482);
x_511 = l_Lean_Syntax_node3(x_482, x_406, x_502, x_506, x_510);
x_512 = l_Lean_Syntax_node2(x_482, x_460, x_497, x_511);
if (lean_is_scalar(x_487)) {
 x_513 = lean_alloc_ctor(0, 2, 0);
} else {
 x_513 = x_487;
}
lean_ctor_set(x_513, 0, x_512);
lean_ctor_set(x_513, 1, x_486);
return x_513;
}
else
{
lean_dec(x_440);
lean_dec(x_431);
lean_dec(x_413);
lean_dec(x_411);
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_406);
lean_dec(x_400);
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_13);
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_441;
}
}
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; uint8_t x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_514 = lean_ctor_get(x_15, 0);
x_515 = lean_ctor_get(x_15, 1);
lean_inc(x_515);
lean_inc(x_514);
lean_dec(x_15);
x_516 = lean_st_ref_get(x_5, x_515);
x_517 = lean_ctor_get(x_516, 1);
lean_inc(x_517);
if (lean_is_exclusive(x_516)) {
 lean_ctor_release(x_516, 0);
 lean_ctor_release(x_516, 1);
 x_518 = x_516;
} else {
 lean_dec_ref(x_516);
 x_518 = lean_box(0);
}
x_519 = lean_ctor_get(x_4, 5);
lean_inc(x_519);
x_520 = lean_box(0);
x_521 = lean_unbox(x_520);
x_522 = l_Lean_SourceInfo_fromRef(x_519, x_521);
lean_dec(x_519);
x_523 = lean_mk_string_unchecked("Lean", 4, 4);
x_524 = lean_mk_string_unchecked("Parser", 6, 6);
x_525 = lean_mk_string_unchecked("Tactic", 6, 6);
x_526 = lean_mk_string_unchecked("attemptAll", 10, 10);
lean_inc(x_525);
lean_inc(x_524);
lean_inc(x_523);
x_527 = l_Lean_Name_mkStr4(x_523, x_524, x_525, x_526);
x_528 = lean_mk_string_unchecked("attempt_all", 11, 11);
lean_inc(x_522);
if (lean_is_scalar(x_518)) {
 x_529 = lean_alloc_ctor(2, 2, 0);
} else {
 x_529 = x_518;
 lean_ctor_set_tag(x_529, 2);
}
lean_ctor_set(x_529, 0, x_522);
lean_ctor_set(x_529, 1, x_528);
x_530 = lean_mk_string_unchecked("null", 4, 4);
x_531 = l_Lean_Name_mkStr1(x_530);
x_532 = lean_mk_string_unchecked("group", 5, 5);
x_533 = l_Lean_Name_mkStr1(x_532);
x_534 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_534);
lean_inc(x_522);
x_535 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_535, 0, x_522);
lean_ctor_set(x_535, 1, x_534);
x_536 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_525);
lean_inc(x_524);
lean_inc(x_523);
x_537 = l_Lean_Name_mkStr4(x_523, x_524, x_525, x_536);
x_538 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_525);
lean_inc(x_524);
lean_inc(x_523);
x_539 = l_Lean_Name_mkStr4(x_523, x_524, x_525, x_538);
lean_inc(x_9);
lean_inc(x_531);
lean_inc(x_522);
x_540 = l_Lean_Syntax_node1(x_522, x_531, x_9);
lean_inc(x_539);
lean_inc(x_522);
x_541 = l_Lean_Syntax_node1(x_522, x_539, x_540);
lean_inc(x_537);
lean_inc(x_522);
x_542 = l_Lean_Syntax_node1(x_522, x_537, x_541);
lean_inc(x_535);
lean_inc(x_533);
lean_inc(x_522);
x_543 = l_Lean_Syntax_node2(x_522, x_533, x_535, x_542);
lean_inc(x_13);
lean_inc(x_531);
lean_inc(x_522);
x_544 = l_Lean_Syntax_node1(x_522, x_531, x_13);
lean_inc(x_539);
lean_inc(x_522);
x_545 = l_Lean_Syntax_node1(x_522, x_539, x_544);
lean_inc(x_537);
lean_inc(x_522);
x_546 = l_Lean_Syntax_node1(x_522, x_537, x_545);
lean_inc(x_535);
lean_inc(x_533);
lean_inc(x_522);
x_547 = l_Lean_Syntax_node2(x_522, x_533, x_535, x_546);
lean_inc(x_531);
lean_inc(x_522);
x_548 = l_Lean_Syntax_node1(x_522, x_531, x_514);
lean_inc(x_539);
lean_inc(x_522);
x_549 = l_Lean_Syntax_node1(x_522, x_539, x_548);
lean_inc(x_537);
lean_inc(x_522);
x_550 = l_Lean_Syntax_node1(x_522, x_537, x_549);
lean_inc(x_535);
lean_inc(x_533);
lean_inc(x_522);
x_551 = l_Lean_Syntax_node2(x_522, x_533, x_535, x_550);
x_552 = lean_mk_string_unchecked("simpAll", 7, 7);
lean_inc(x_525);
lean_inc(x_524);
lean_inc(x_523);
x_553 = l_Lean_Name_mkStr4(x_523, x_524, x_525, x_552);
x_554 = lean_mk_string_unchecked("simp_all", 8, 8);
lean_inc(x_522);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_554);
lean_ctor_set(x_11, 0, x_522);
x_555 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_525);
lean_inc(x_524);
lean_inc(x_523);
x_556 = l_Lean_Name_mkStr4(x_523, x_524, x_525, x_555);
x_557 = l_Array_mkArray0(lean_box(0));
lean_inc(x_557);
lean_inc(x_531);
lean_inc(x_522);
x_558 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_558, 0, x_522);
lean_ctor_set(x_558, 1, x_531);
lean_ctor_set(x_558, 2, x_557);
lean_inc(x_558);
lean_inc(x_522);
x_559 = l_Lean_Syntax_node1(x_522, x_556, x_558);
lean_inc_n(x_558, 2);
lean_inc(x_522);
x_560 = l_Lean_Syntax_node5(x_522, x_553, x_11, x_559, x_558, x_558, x_558);
lean_inc(x_531);
lean_inc(x_522);
x_561 = l_Lean_Syntax_node1(x_522, x_531, x_560);
lean_inc(x_539);
lean_inc(x_522);
x_562 = l_Lean_Syntax_node1(x_522, x_539, x_561);
lean_inc(x_537);
lean_inc(x_522);
x_563 = l_Lean_Syntax_node1(x_522, x_537, x_562);
lean_inc(x_533);
lean_inc(x_522);
x_564 = l_Lean_Syntax_node2(x_522, x_533, x_535, x_563);
lean_inc(x_531);
lean_inc(x_522);
x_565 = l_Lean_Syntax_node4(x_522, x_531, x_543, x_547, x_551, x_564);
x_566 = l_Lean_Syntax_node2(x_522, x_527, x_529, x_565);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_566);
x_567 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx(x_1, x_566, x_2, x_3, x_4, x_5, x_517);
if (lean_obj_tag(x_567) == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_567, 1);
lean_inc(x_569);
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 lean_ctor_release(x_567, 1);
 x_570 = x_567;
} else {
 lean_dec_ref(x_567);
 x_570 = lean_box(0);
}
x_571 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___lam__0(x_2, x_3, x_4, x_5, x_569);
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
x_573 = lean_ctor_get(x_571, 1);
lean_inc(x_573);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 lean_ctor_release(x_571, 1);
 x_574 = x_571;
} else {
 lean_dec_ref(x_571);
 x_574 = lean_box(0);
}
x_575 = lean_st_ref_get(x_5, x_573);
x_576 = lean_ctor_get(x_575, 1);
lean_inc(x_576);
if (lean_is_exclusive(x_575)) {
 lean_ctor_release(x_575, 0);
 lean_ctor_release(x_575, 1);
 x_577 = x_575;
} else {
 lean_dec_ref(x_575);
 x_577 = lean_box(0);
}
x_578 = lean_mk_string_unchecked("intros", 6, 6);
lean_inc(x_578);
lean_inc(x_525);
lean_inc(x_524);
lean_inc(x_523);
x_579 = l_Lean_Name_mkStr4(x_523, x_524, x_525, x_578);
lean_inc(x_572);
if (lean_is_scalar(x_577)) {
 x_580 = lean_alloc_ctor(2, 2, 0);
} else {
 x_580 = x_577;
 lean_ctor_set_tag(x_580, 2);
}
lean_ctor_set(x_580, 0, x_572);
lean_ctor_set(x_580, 1, x_578);
lean_inc(x_531);
lean_inc(x_572);
x_581 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_581, 0, x_572);
lean_ctor_set(x_581, 1, x_531);
lean_ctor_set(x_581, 2, x_557);
lean_inc(x_581);
lean_inc(x_572);
x_582 = l_Lean_Syntax_node2(x_572, x_579, x_580, x_581);
x_583 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_572);
if (lean_is_scalar(x_574)) {
 x_584 = lean_alloc_ctor(2, 2, 0);
} else {
 x_584 = x_574;
 lean_ctor_set_tag(x_584, 2);
}
lean_ctor_set(x_584, 0, x_572);
lean_ctor_set(x_584, 1, x_583);
x_585 = lean_mk_string_unchecked("first", 5, 5);
lean_inc(x_585);
lean_inc(x_525);
lean_inc(x_524);
lean_inc(x_523);
x_586 = l_Lean_Name_mkStr4(x_523, x_524, x_525, x_585);
lean_inc(x_585);
lean_inc(x_572);
if (lean_is_scalar(x_570)) {
 x_587 = lean_alloc_ctor(2, 2, 0);
} else {
 x_587 = x_570;
 lean_ctor_set_tag(x_587, 2);
}
lean_ctor_set(x_587, 0, x_572);
lean_ctor_set(x_587, 1, x_585);
lean_inc(x_534);
lean_inc(x_572);
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_534);
lean_ctor_set(x_7, 0, x_572);
lean_inc(x_531);
lean_inc(x_572);
x_588 = l_Lean_Syntax_node1(x_572, x_531, x_9);
lean_inc(x_539);
lean_inc(x_572);
x_589 = l_Lean_Syntax_node1(x_572, x_539, x_588);
lean_inc(x_537);
lean_inc(x_572);
x_590 = l_Lean_Syntax_node1(x_572, x_537, x_589);
lean_inc(x_7);
lean_inc(x_533);
lean_inc(x_572);
x_591 = l_Lean_Syntax_node2(x_572, x_533, x_7, x_590);
lean_inc(x_531);
lean_inc(x_572);
x_592 = l_Lean_Syntax_node1(x_572, x_531, x_13);
lean_inc(x_539);
lean_inc(x_572);
x_593 = l_Lean_Syntax_node1(x_572, x_539, x_592);
lean_inc(x_537);
lean_inc(x_572);
x_594 = l_Lean_Syntax_node1(x_572, x_537, x_593);
lean_inc(x_7);
lean_inc(x_533);
lean_inc(x_572);
x_595 = l_Lean_Syntax_node2(x_572, x_533, x_7, x_594);
x_596 = lean_mk_string_unchecked("exact\?", 6, 6);
lean_inc(x_596);
lean_inc(x_525);
lean_inc(x_524);
lean_inc(x_523);
x_597 = l_Lean_Name_mkStr4(x_523, x_524, x_525, x_596);
lean_inc(x_572);
x_598 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_598, 0, x_572);
lean_ctor_set(x_598, 1, x_596);
lean_inc(x_572);
x_599 = l_Lean_Syntax_node2(x_572, x_597, x_598, x_581);
lean_inc(x_531);
lean_inc(x_572);
x_600 = l_Lean_Syntax_node1(x_572, x_531, x_599);
lean_inc(x_539);
lean_inc(x_572);
x_601 = l_Lean_Syntax_node1(x_572, x_539, x_600);
lean_inc(x_537);
lean_inc(x_572);
x_602 = l_Lean_Syntax_node1(x_572, x_537, x_601);
lean_inc(x_533);
lean_inc(x_572);
x_603 = l_Lean_Syntax_node2(x_572, x_533, x_7, x_602);
lean_inc(x_531);
lean_inc(x_572);
x_604 = l_Lean_Syntax_node3(x_572, x_531, x_591, x_595, x_603);
lean_inc(x_586);
lean_inc(x_572);
x_605 = l_Lean_Syntax_node2(x_572, x_586, x_587, x_604);
lean_inc(x_531);
lean_inc(x_572);
x_606 = l_Lean_Syntax_node3(x_572, x_531, x_582, x_584, x_605);
x_607 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___lam__0(x_2, x_3, x_4, x_5, x_576);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_608 = lean_ctor_get(x_607, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_607, 1);
lean_inc(x_609);
if (lean_is_exclusive(x_607)) {
 lean_ctor_release(x_607, 0);
 lean_ctor_release(x_607, 1);
 x_610 = x_607;
} else {
 lean_dec_ref(x_607);
 x_610 = lean_box(0);
}
x_611 = lean_st_ref_get(x_5, x_609);
lean_dec(x_5);
x_612 = lean_ctor_get(x_611, 1);
lean_inc(x_612);
if (lean_is_exclusive(x_611)) {
 lean_ctor_release(x_611, 0);
 lean_ctor_release(x_611, 1);
 x_613 = x_611;
} else {
 lean_dec_ref(x_611);
 x_613 = lean_box(0);
}
x_614 = lean_mk_string_unchecked("paren", 5, 5);
x_615 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_539);
lean_inc(x_572);
x_616 = l_Lean_Syntax_node1(x_572, x_539, x_606);
x_617 = lean_mk_string_unchecked(")", 1, 1);
x_618 = l_Lean_Name_mkStr4(x_523, x_524, x_525, x_614);
lean_inc(x_572);
if (lean_is_scalar(x_610)) {
 x_619 = lean_alloc_ctor(2, 2, 0);
} else {
 x_619 = x_610;
 lean_ctor_set_tag(x_619, 2);
}
lean_ctor_set(x_619, 0, x_572);
lean_ctor_set(x_619, 1, x_615);
lean_inc(x_537);
lean_inc(x_572);
x_620 = l_Lean_Syntax_node1(x_572, x_537, x_616);
lean_inc(x_572);
x_621 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_621, 0, x_572);
lean_ctor_set(x_621, 1, x_617);
x_622 = l_Lean_Syntax_node3(x_572, x_618, x_619, x_620, x_621);
lean_inc(x_608);
x_623 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_623, 0, x_608);
lean_ctor_set(x_623, 1, x_585);
lean_inc(x_608);
x_624 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_624, 0, x_608);
lean_ctor_set(x_624, 1, x_534);
lean_inc(x_531);
lean_inc(x_608);
x_625 = l_Lean_Syntax_node1(x_608, x_531, x_566);
lean_inc(x_539);
lean_inc(x_608);
x_626 = l_Lean_Syntax_node1(x_608, x_539, x_625);
lean_inc(x_537);
lean_inc(x_608);
x_627 = l_Lean_Syntax_node1(x_608, x_537, x_626);
lean_inc(x_624);
lean_inc(x_533);
lean_inc(x_608);
x_628 = l_Lean_Syntax_node2(x_608, x_533, x_624, x_627);
lean_inc(x_531);
lean_inc(x_608);
x_629 = l_Lean_Syntax_node1(x_608, x_531, x_568);
lean_inc(x_539);
lean_inc(x_608);
x_630 = l_Lean_Syntax_node1(x_608, x_539, x_629);
lean_inc(x_537);
lean_inc(x_608);
x_631 = l_Lean_Syntax_node1(x_608, x_537, x_630);
lean_inc(x_624);
lean_inc(x_533);
lean_inc(x_608);
x_632 = l_Lean_Syntax_node2(x_608, x_533, x_624, x_631);
lean_inc(x_531);
lean_inc(x_608);
x_633 = l_Lean_Syntax_node1(x_608, x_531, x_622);
lean_inc(x_608);
x_634 = l_Lean_Syntax_node1(x_608, x_539, x_633);
lean_inc(x_608);
x_635 = l_Lean_Syntax_node1(x_608, x_537, x_634);
lean_inc(x_608);
x_636 = l_Lean_Syntax_node2(x_608, x_533, x_624, x_635);
lean_inc(x_608);
x_637 = l_Lean_Syntax_node3(x_608, x_531, x_628, x_632, x_636);
x_638 = l_Lean_Syntax_node2(x_608, x_586, x_623, x_637);
if (lean_is_scalar(x_613)) {
 x_639 = lean_alloc_ctor(0, 2, 0);
} else {
 x_639 = x_613;
}
lean_ctor_set(x_639, 0, x_638);
lean_ctor_set(x_639, 1, x_612);
return x_639;
}
else
{
lean_dec(x_566);
lean_dec(x_557);
lean_dec(x_539);
lean_dec(x_537);
lean_dec(x_534);
lean_dec(x_533);
lean_dec(x_531);
lean_dec(x_525);
lean_dec(x_524);
lean_dec(x_523);
lean_dec(x_13);
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_567;
}
}
}
else
{
lean_free_object(x_11);
lean_dec(x_13);
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_640 = lean_ctor_get(x_11, 0);
x_641 = lean_ctor_get(x_11, 1);
lean_inc(x_641);
lean_inc(x_640);
lean_dec(x_11);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_642 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx(x_1, x_2, x_3, x_4, x_5, x_641);
if (lean_obj_tag(x_642) == 0)
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; uint8_t x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_643 = lean_ctor_get(x_642, 0);
lean_inc(x_643);
x_644 = lean_ctor_get(x_642, 1);
lean_inc(x_644);
if (lean_is_exclusive(x_642)) {
 lean_ctor_release(x_642, 0);
 lean_ctor_release(x_642, 1);
 x_645 = x_642;
} else {
 lean_dec_ref(x_642);
 x_645 = lean_box(0);
}
x_646 = lean_st_ref_get(x_5, x_644);
x_647 = lean_ctor_get(x_646, 1);
lean_inc(x_647);
if (lean_is_exclusive(x_646)) {
 lean_ctor_release(x_646, 0);
 lean_ctor_release(x_646, 1);
 x_648 = x_646;
} else {
 lean_dec_ref(x_646);
 x_648 = lean_box(0);
}
x_649 = lean_ctor_get(x_4, 5);
lean_inc(x_649);
x_650 = lean_box(0);
x_651 = lean_unbox(x_650);
x_652 = l_Lean_SourceInfo_fromRef(x_649, x_651);
lean_dec(x_649);
x_653 = lean_mk_string_unchecked("Lean", 4, 4);
x_654 = lean_mk_string_unchecked("Parser", 6, 6);
x_655 = lean_mk_string_unchecked("Tactic", 6, 6);
x_656 = lean_mk_string_unchecked("attemptAll", 10, 10);
lean_inc(x_655);
lean_inc(x_654);
lean_inc(x_653);
x_657 = l_Lean_Name_mkStr4(x_653, x_654, x_655, x_656);
x_658 = lean_mk_string_unchecked("attempt_all", 11, 11);
lean_inc(x_652);
if (lean_is_scalar(x_648)) {
 x_659 = lean_alloc_ctor(2, 2, 0);
} else {
 x_659 = x_648;
 lean_ctor_set_tag(x_659, 2);
}
lean_ctor_set(x_659, 0, x_652);
lean_ctor_set(x_659, 1, x_658);
x_660 = lean_mk_string_unchecked("null", 4, 4);
x_661 = l_Lean_Name_mkStr1(x_660);
x_662 = lean_mk_string_unchecked("group", 5, 5);
x_663 = l_Lean_Name_mkStr1(x_662);
x_664 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_664);
lean_inc(x_652);
if (lean_is_scalar(x_645)) {
 x_665 = lean_alloc_ctor(2, 2, 0);
} else {
 x_665 = x_645;
 lean_ctor_set_tag(x_665, 2);
}
lean_ctor_set(x_665, 0, x_652);
lean_ctor_set(x_665, 1, x_664);
x_666 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_655);
lean_inc(x_654);
lean_inc(x_653);
x_667 = l_Lean_Name_mkStr4(x_653, x_654, x_655, x_666);
x_668 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_655);
lean_inc(x_654);
lean_inc(x_653);
x_669 = l_Lean_Name_mkStr4(x_653, x_654, x_655, x_668);
lean_inc(x_9);
lean_inc(x_661);
lean_inc(x_652);
x_670 = l_Lean_Syntax_node1(x_652, x_661, x_9);
lean_inc(x_669);
lean_inc(x_652);
x_671 = l_Lean_Syntax_node1(x_652, x_669, x_670);
lean_inc(x_667);
lean_inc(x_652);
x_672 = l_Lean_Syntax_node1(x_652, x_667, x_671);
lean_inc(x_665);
lean_inc(x_663);
lean_inc(x_652);
x_673 = l_Lean_Syntax_node2(x_652, x_663, x_665, x_672);
lean_inc(x_640);
lean_inc(x_661);
lean_inc(x_652);
x_674 = l_Lean_Syntax_node1(x_652, x_661, x_640);
lean_inc(x_669);
lean_inc(x_652);
x_675 = l_Lean_Syntax_node1(x_652, x_669, x_674);
lean_inc(x_667);
lean_inc(x_652);
x_676 = l_Lean_Syntax_node1(x_652, x_667, x_675);
lean_inc(x_665);
lean_inc(x_663);
lean_inc(x_652);
x_677 = l_Lean_Syntax_node2(x_652, x_663, x_665, x_676);
lean_inc(x_661);
lean_inc(x_652);
x_678 = l_Lean_Syntax_node1(x_652, x_661, x_643);
lean_inc(x_669);
lean_inc(x_652);
x_679 = l_Lean_Syntax_node1(x_652, x_669, x_678);
lean_inc(x_667);
lean_inc(x_652);
x_680 = l_Lean_Syntax_node1(x_652, x_667, x_679);
lean_inc(x_665);
lean_inc(x_663);
lean_inc(x_652);
x_681 = l_Lean_Syntax_node2(x_652, x_663, x_665, x_680);
x_682 = lean_mk_string_unchecked("simpAll", 7, 7);
lean_inc(x_655);
lean_inc(x_654);
lean_inc(x_653);
x_683 = l_Lean_Name_mkStr4(x_653, x_654, x_655, x_682);
x_684 = lean_mk_string_unchecked("simp_all", 8, 8);
lean_inc(x_652);
x_685 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_685, 0, x_652);
lean_ctor_set(x_685, 1, x_684);
x_686 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_655);
lean_inc(x_654);
lean_inc(x_653);
x_687 = l_Lean_Name_mkStr4(x_653, x_654, x_655, x_686);
x_688 = l_Array_mkArray0(lean_box(0));
lean_inc(x_688);
lean_inc(x_661);
lean_inc(x_652);
x_689 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_689, 0, x_652);
lean_ctor_set(x_689, 1, x_661);
lean_ctor_set(x_689, 2, x_688);
lean_inc(x_689);
lean_inc(x_652);
x_690 = l_Lean_Syntax_node1(x_652, x_687, x_689);
lean_inc_n(x_689, 2);
lean_inc(x_652);
x_691 = l_Lean_Syntax_node5(x_652, x_683, x_685, x_690, x_689, x_689, x_689);
lean_inc(x_661);
lean_inc(x_652);
x_692 = l_Lean_Syntax_node1(x_652, x_661, x_691);
lean_inc(x_669);
lean_inc(x_652);
x_693 = l_Lean_Syntax_node1(x_652, x_669, x_692);
lean_inc(x_667);
lean_inc(x_652);
x_694 = l_Lean_Syntax_node1(x_652, x_667, x_693);
lean_inc(x_663);
lean_inc(x_652);
x_695 = l_Lean_Syntax_node2(x_652, x_663, x_665, x_694);
lean_inc(x_661);
lean_inc(x_652);
x_696 = l_Lean_Syntax_node4(x_652, x_661, x_673, x_677, x_681, x_695);
x_697 = l_Lean_Syntax_node2(x_652, x_657, x_659, x_696);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_697);
x_698 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx(x_1, x_697, x_2, x_3, x_4, x_5, x_647);
if (lean_obj_tag(x_698) == 0)
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; 
x_699 = lean_ctor_get(x_698, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_698, 1);
lean_inc(x_700);
if (lean_is_exclusive(x_698)) {
 lean_ctor_release(x_698, 0);
 lean_ctor_release(x_698, 1);
 x_701 = x_698;
} else {
 lean_dec_ref(x_698);
 x_701 = lean_box(0);
}
x_702 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___lam__0(x_2, x_3, x_4, x_5, x_700);
x_703 = lean_ctor_get(x_702, 0);
lean_inc(x_703);
x_704 = lean_ctor_get(x_702, 1);
lean_inc(x_704);
if (lean_is_exclusive(x_702)) {
 lean_ctor_release(x_702, 0);
 lean_ctor_release(x_702, 1);
 x_705 = x_702;
} else {
 lean_dec_ref(x_702);
 x_705 = lean_box(0);
}
x_706 = lean_st_ref_get(x_5, x_704);
x_707 = lean_ctor_get(x_706, 1);
lean_inc(x_707);
if (lean_is_exclusive(x_706)) {
 lean_ctor_release(x_706, 0);
 lean_ctor_release(x_706, 1);
 x_708 = x_706;
} else {
 lean_dec_ref(x_706);
 x_708 = lean_box(0);
}
x_709 = lean_mk_string_unchecked("intros", 6, 6);
lean_inc(x_709);
lean_inc(x_655);
lean_inc(x_654);
lean_inc(x_653);
x_710 = l_Lean_Name_mkStr4(x_653, x_654, x_655, x_709);
lean_inc(x_703);
if (lean_is_scalar(x_708)) {
 x_711 = lean_alloc_ctor(2, 2, 0);
} else {
 x_711 = x_708;
 lean_ctor_set_tag(x_711, 2);
}
lean_ctor_set(x_711, 0, x_703);
lean_ctor_set(x_711, 1, x_709);
lean_inc(x_661);
lean_inc(x_703);
x_712 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_712, 0, x_703);
lean_ctor_set(x_712, 1, x_661);
lean_ctor_set(x_712, 2, x_688);
lean_inc(x_712);
lean_inc(x_703);
x_713 = l_Lean_Syntax_node2(x_703, x_710, x_711, x_712);
x_714 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_703);
if (lean_is_scalar(x_705)) {
 x_715 = lean_alloc_ctor(2, 2, 0);
} else {
 x_715 = x_705;
 lean_ctor_set_tag(x_715, 2);
}
lean_ctor_set(x_715, 0, x_703);
lean_ctor_set(x_715, 1, x_714);
x_716 = lean_mk_string_unchecked("first", 5, 5);
lean_inc(x_716);
lean_inc(x_655);
lean_inc(x_654);
lean_inc(x_653);
x_717 = l_Lean_Name_mkStr4(x_653, x_654, x_655, x_716);
lean_inc(x_716);
lean_inc(x_703);
if (lean_is_scalar(x_701)) {
 x_718 = lean_alloc_ctor(2, 2, 0);
} else {
 x_718 = x_701;
 lean_ctor_set_tag(x_718, 2);
}
lean_ctor_set(x_718, 0, x_703);
lean_ctor_set(x_718, 1, x_716);
lean_inc(x_664);
lean_inc(x_703);
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_664);
lean_ctor_set(x_7, 0, x_703);
lean_inc(x_661);
lean_inc(x_703);
x_719 = l_Lean_Syntax_node1(x_703, x_661, x_9);
lean_inc(x_669);
lean_inc(x_703);
x_720 = l_Lean_Syntax_node1(x_703, x_669, x_719);
lean_inc(x_667);
lean_inc(x_703);
x_721 = l_Lean_Syntax_node1(x_703, x_667, x_720);
lean_inc(x_7);
lean_inc(x_663);
lean_inc(x_703);
x_722 = l_Lean_Syntax_node2(x_703, x_663, x_7, x_721);
lean_inc(x_661);
lean_inc(x_703);
x_723 = l_Lean_Syntax_node1(x_703, x_661, x_640);
lean_inc(x_669);
lean_inc(x_703);
x_724 = l_Lean_Syntax_node1(x_703, x_669, x_723);
lean_inc(x_667);
lean_inc(x_703);
x_725 = l_Lean_Syntax_node1(x_703, x_667, x_724);
lean_inc(x_7);
lean_inc(x_663);
lean_inc(x_703);
x_726 = l_Lean_Syntax_node2(x_703, x_663, x_7, x_725);
x_727 = lean_mk_string_unchecked("exact\?", 6, 6);
lean_inc(x_727);
lean_inc(x_655);
lean_inc(x_654);
lean_inc(x_653);
x_728 = l_Lean_Name_mkStr4(x_653, x_654, x_655, x_727);
lean_inc(x_703);
x_729 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_729, 0, x_703);
lean_ctor_set(x_729, 1, x_727);
lean_inc(x_703);
x_730 = l_Lean_Syntax_node2(x_703, x_728, x_729, x_712);
lean_inc(x_661);
lean_inc(x_703);
x_731 = l_Lean_Syntax_node1(x_703, x_661, x_730);
lean_inc(x_669);
lean_inc(x_703);
x_732 = l_Lean_Syntax_node1(x_703, x_669, x_731);
lean_inc(x_667);
lean_inc(x_703);
x_733 = l_Lean_Syntax_node1(x_703, x_667, x_732);
lean_inc(x_663);
lean_inc(x_703);
x_734 = l_Lean_Syntax_node2(x_703, x_663, x_7, x_733);
lean_inc(x_661);
lean_inc(x_703);
x_735 = l_Lean_Syntax_node3(x_703, x_661, x_722, x_726, x_734);
lean_inc(x_717);
lean_inc(x_703);
x_736 = l_Lean_Syntax_node2(x_703, x_717, x_718, x_735);
lean_inc(x_661);
lean_inc(x_703);
x_737 = l_Lean_Syntax_node3(x_703, x_661, x_713, x_715, x_736);
x_738 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___lam__0(x_2, x_3, x_4, x_5, x_707);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_739 = lean_ctor_get(x_738, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_738, 1);
lean_inc(x_740);
if (lean_is_exclusive(x_738)) {
 lean_ctor_release(x_738, 0);
 lean_ctor_release(x_738, 1);
 x_741 = x_738;
} else {
 lean_dec_ref(x_738);
 x_741 = lean_box(0);
}
x_742 = lean_st_ref_get(x_5, x_740);
lean_dec(x_5);
x_743 = lean_ctor_get(x_742, 1);
lean_inc(x_743);
if (lean_is_exclusive(x_742)) {
 lean_ctor_release(x_742, 0);
 lean_ctor_release(x_742, 1);
 x_744 = x_742;
} else {
 lean_dec_ref(x_742);
 x_744 = lean_box(0);
}
x_745 = lean_mk_string_unchecked("paren", 5, 5);
x_746 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_669);
lean_inc(x_703);
x_747 = l_Lean_Syntax_node1(x_703, x_669, x_737);
x_748 = lean_mk_string_unchecked(")", 1, 1);
x_749 = l_Lean_Name_mkStr4(x_653, x_654, x_655, x_745);
lean_inc(x_703);
if (lean_is_scalar(x_741)) {
 x_750 = lean_alloc_ctor(2, 2, 0);
} else {
 x_750 = x_741;
 lean_ctor_set_tag(x_750, 2);
}
lean_ctor_set(x_750, 0, x_703);
lean_ctor_set(x_750, 1, x_746);
lean_inc(x_667);
lean_inc(x_703);
x_751 = l_Lean_Syntax_node1(x_703, x_667, x_747);
lean_inc(x_703);
x_752 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_752, 0, x_703);
lean_ctor_set(x_752, 1, x_748);
x_753 = l_Lean_Syntax_node3(x_703, x_749, x_750, x_751, x_752);
lean_inc(x_739);
x_754 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_754, 0, x_739);
lean_ctor_set(x_754, 1, x_716);
lean_inc(x_739);
x_755 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_755, 0, x_739);
lean_ctor_set(x_755, 1, x_664);
lean_inc(x_661);
lean_inc(x_739);
x_756 = l_Lean_Syntax_node1(x_739, x_661, x_697);
lean_inc(x_669);
lean_inc(x_739);
x_757 = l_Lean_Syntax_node1(x_739, x_669, x_756);
lean_inc(x_667);
lean_inc(x_739);
x_758 = l_Lean_Syntax_node1(x_739, x_667, x_757);
lean_inc(x_755);
lean_inc(x_663);
lean_inc(x_739);
x_759 = l_Lean_Syntax_node2(x_739, x_663, x_755, x_758);
lean_inc(x_661);
lean_inc(x_739);
x_760 = l_Lean_Syntax_node1(x_739, x_661, x_699);
lean_inc(x_669);
lean_inc(x_739);
x_761 = l_Lean_Syntax_node1(x_739, x_669, x_760);
lean_inc(x_667);
lean_inc(x_739);
x_762 = l_Lean_Syntax_node1(x_739, x_667, x_761);
lean_inc(x_755);
lean_inc(x_663);
lean_inc(x_739);
x_763 = l_Lean_Syntax_node2(x_739, x_663, x_755, x_762);
lean_inc(x_661);
lean_inc(x_739);
x_764 = l_Lean_Syntax_node1(x_739, x_661, x_753);
lean_inc(x_739);
x_765 = l_Lean_Syntax_node1(x_739, x_669, x_764);
lean_inc(x_739);
x_766 = l_Lean_Syntax_node1(x_739, x_667, x_765);
lean_inc(x_739);
x_767 = l_Lean_Syntax_node2(x_739, x_663, x_755, x_766);
lean_inc(x_739);
x_768 = l_Lean_Syntax_node3(x_739, x_661, x_759, x_763, x_767);
x_769 = l_Lean_Syntax_node2(x_739, x_717, x_754, x_768);
if (lean_is_scalar(x_744)) {
 x_770 = lean_alloc_ctor(0, 2, 0);
} else {
 x_770 = x_744;
}
lean_ctor_set(x_770, 0, x_769);
lean_ctor_set(x_770, 1, x_743);
return x_770;
}
else
{
lean_dec(x_697);
lean_dec(x_688);
lean_dec(x_669);
lean_dec(x_667);
lean_dec(x_664);
lean_dec(x_663);
lean_dec(x_661);
lean_dec(x_655);
lean_dec(x_654);
lean_dec(x_653);
lean_dec(x_640);
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_698;
}
}
else
{
lean_dec(x_640);
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_642;
}
}
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; 
x_771 = lean_ctor_get(x_7, 0);
x_772 = lean_ctor_get(x_7, 1);
lean_inc(x_772);
lean_inc(x_771);
lean_dec(x_7);
x_773 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx(x_4, x_5, x_772);
x_774 = lean_ctor_get(x_773, 0);
lean_inc(x_774);
x_775 = lean_ctor_get(x_773, 1);
lean_inc(x_775);
if (lean_is_exclusive(x_773)) {
 lean_ctor_release(x_773, 0);
 lean_ctor_release(x_773, 1);
 x_776 = x_773;
} else {
 lean_dec_ref(x_773);
 x_776 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_777 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx(x_1, x_2, x_3, x_4, x_5, x_775);
if (lean_obj_tag(x_777) == 0)
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; uint8_t x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; 
x_778 = lean_ctor_get(x_777, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_777, 1);
lean_inc(x_779);
if (lean_is_exclusive(x_777)) {
 lean_ctor_release(x_777, 0);
 lean_ctor_release(x_777, 1);
 x_780 = x_777;
} else {
 lean_dec_ref(x_777);
 x_780 = lean_box(0);
}
x_781 = lean_st_ref_get(x_5, x_779);
x_782 = lean_ctor_get(x_781, 1);
lean_inc(x_782);
if (lean_is_exclusive(x_781)) {
 lean_ctor_release(x_781, 0);
 lean_ctor_release(x_781, 1);
 x_783 = x_781;
} else {
 lean_dec_ref(x_781);
 x_783 = lean_box(0);
}
x_784 = lean_ctor_get(x_4, 5);
lean_inc(x_784);
x_785 = lean_box(0);
x_786 = lean_unbox(x_785);
x_787 = l_Lean_SourceInfo_fromRef(x_784, x_786);
lean_dec(x_784);
x_788 = lean_mk_string_unchecked("Lean", 4, 4);
x_789 = lean_mk_string_unchecked("Parser", 6, 6);
x_790 = lean_mk_string_unchecked("Tactic", 6, 6);
x_791 = lean_mk_string_unchecked("attemptAll", 10, 10);
lean_inc(x_790);
lean_inc(x_789);
lean_inc(x_788);
x_792 = l_Lean_Name_mkStr4(x_788, x_789, x_790, x_791);
x_793 = lean_mk_string_unchecked("attempt_all", 11, 11);
lean_inc(x_787);
if (lean_is_scalar(x_783)) {
 x_794 = lean_alloc_ctor(2, 2, 0);
} else {
 x_794 = x_783;
 lean_ctor_set_tag(x_794, 2);
}
lean_ctor_set(x_794, 0, x_787);
lean_ctor_set(x_794, 1, x_793);
x_795 = lean_mk_string_unchecked("null", 4, 4);
x_796 = l_Lean_Name_mkStr1(x_795);
x_797 = lean_mk_string_unchecked("group", 5, 5);
x_798 = l_Lean_Name_mkStr1(x_797);
x_799 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_799);
lean_inc(x_787);
if (lean_is_scalar(x_780)) {
 x_800 = lean_alloc_ctor(2, 2, 0);
} else {
 x_800 = x_780;
 lean_ctor_set_tag(x_800, 2);
}
lean_ctor_set(x_800, 0, x_787);
lean_ctor_set(x_800, 1, x_799);
x_801 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_790);
lean_inc(x_789);
lean_inc(x_788);
x_802 = l_Lean_Name_mkStr4(x_788, x_789, x_790, x_801);
x_803 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_790);
lean_inc(x_789);
lean_inc(x_788);
x_804 = l_Lean_Name_mkStr4(x_788, x_789, x_790, x_803);
lean_inc(x_771);
lean_inc(x_796);
lean_inc(x_787);
x_805 = l_Lean_Syntax_node1(x_787, x_796, x_771);
lean_inc(x_804);
lean_inc(x_787);
x_806 = l_Lean_Syntax_node1(x_787, x_804, x_805);
lean_inc(x_802);
lean_inc(x_787);
x_807 = l_Lean_Syntax_node1(x_787, x_802, x_806);
lean_inc(x_800);
lean_inc(x_798);
lean_inc(x_787);
x_808 = l_Lean_Syntax_node2(x_787, x_798, x_800, x_807);
lean_inc(x_774);
lean_inc(x_796);
lean_inc(x_787);
x_809 = l_Lean_Syntax_node1(x_787, x_796, x_774);
lean_inc(x_804);
lean_inc(x_787);
x_810 = l_Lean_Syntax_node1(x_787, x_804, x_809);
lean_inc(x_802);
lean_inc(x_787);
x_811 = l_Lean_Syntax_node1(x_787, x_802, x_810);
lean_inc(x_800);
lean_inc(x_798);
lean_inc(x_787);
x_812 = l_Lean_Syntax_node2(x_787, x_798, x_800, x_811);
lean_inc(x_796);
lean_inc(x_787);
x_813 = l_Lean_Syntax_node1(x_787, x_796, x_778);
lean_inc(x_804);
lean_inc(x_787);
x_814 = l_Lean_Syntax_node1(x_787, x_804, x_813);
lean_inc(x_802);
lean_inc(x_787);
x_815 = l_Lean_Syntax_node1(x_787, x_802, x_814);
lean_inc(x_800);
lean_inc(x_798);
lean_inc(x_787);
x_816 = l_Lean_Syntax_node2(x_787, x_798, x_800, x_815);
x_817 = lean_mk_string_unchecked("simpAll", 7, 7);
lean_inc(x_790);
lean_inc(x_789);
lean_inc(x_788);
x_818 = l_Lean_Name_mkStr4(x_788, x_789, x_790, x_817);
x_819 = lean_mk_string_unchecked("simp_all", 8, 8);
lean_inc(x_787);
if (lean_is_scalar(x_776)) {
 x_820 = lean_alloc_ctor(2, 2, 0);
} else {
 x_820 = x_776;
 lean_ctor_set_tag(x_820, 2);
}
lean_ctor_set(x_820, 0, x_787);
lean_ctor_set(x_820, 1, x_819);
x_821 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_790);
lean_inc(x_789);
lean_inc(x_788);
x_822 = l_Lean_Name_mkStr4(x_788, x_789, x_790, x_821);
x_823 = l_Array_mkArray0(lean_box(0));
lean_inc(x_823);
lean_inc(x_796);
lean_inc(x_787);
x_824 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_824, 0, x_787);
lean_ctor_set(x_824, 1, x_796);
lean_ctor_set(x_824, 2, x_823);
lean_inc(x_824);
lean_inc(x_787);
x_825 = l_Lean_Syntax_node1(x_787, x_822, x_824);
lean_inc_n(x_824, 2);
lean_inc(x_787);
x_826 = l_Lean_Syntax_node5(x_787, x_818, x_820, x_825, x_824, x_824, x_824);
lean_inc(x_796);
lean_inc(x_787);
x_827 = l_Lean_Syntax_node1(x_787, x_796, x_826);
lean_inc(x_804);
lean_inc(x_787);
x_828 = l_Lean_Syntax_node1(x_787, x_804, x_827);
lean_inc(x_802);
lean_inc(x_787);
x_829 = l_Lean_Syntax_node1(x_787, x_802, x_828);
lean_inc(x_798);
lean_inc(x_787);
x_830 = l_Lean_Syntax_node2(x_787, x_798, x_800, x_829);
lean_inc(x_796);
lean_inc(x_787);
x_831 = l_Lean_Syntax_node4(x_787, x_796, x_808, x_812, x_816, x_830);
x_832 = l_Lean_Syntax_node2(x_787, x_792, x_794, x_831);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_832);
x_833 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx(x_1, x_832, x_2, x_3, x_4, x_5, x_782);
if (lean_obj_tag(x_833) == 0)
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; 
x_834 = lean_ctor_get(x_833, 0);
lean_inc(x_834);
x_835 = lean_ctor_get(x_833, 1);
lean_inc(x_835);
if (lean_is_exclusive(x_833)) {
 lean_ctor_release(x_833, 0);
 lean_ctor_release(x_833, 1);
 x_836 = x_833;
} else {
 lean_dec_ref(x_833);
 x_836 = lean_box(0);
}
x_837 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___lam__0(x_2, x_3, x_4, x_5, x_835);
x_838 = lean_ctor_get(x_837, 0);
lean_inc(x_838);
x_839 = lean_ctor_get(x_837, 1);
lean_inc(x_839);
if (lean_is_exclusive(x_837)) {
 lean_ctor_release(x_837, 0);
 lean_ctor_release(x_837, 1);
 x_840 = x_837;
} else {
 lean_dec_ref(x_837);
 x_840 = lean_box(0);
}
x_841 = lean_st_ref_get(x_5, x_839);
x_842 = lean_ctor_get(x_841, 1);
lean_inc(x_842);
if (lean_is_exclusive(x_841)) {
 lean_ctor_release(x_841, 0);
 lean_ctor_release(x_841, 1);
 x_843 = x_841;
} else {
 lean_dec_ref(x_841);
 x_843 = lean_box(0);
}
x_844 = lean_mk_string_unchecked("intros", 6, 6);
lean_inc(x_844);
lean_inc(x_790);
lean_inc(x_789);
lean_inc(x_788);
x_845 = l_Lean_Name_mkStr4(x_788, x_789, x_790, x_844);
lean_inc(x_838);
if (lean_is_scalar(x_843)) {
 x_846 = lean_alloc_ctor(2, 2, 0);
} else {
 x_846 = x_843;
 lean_ctor_set_tag(x_846, 2);
}
lean_ctor_set(x_846, 0, x_838);
lean_ctor_set(x_846, 1, x_844);
lean_inc(x_796);
lean_inc(x_838);
x_847 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_847, 0, x_838);
lean_ctor_set(x_847, 1, x_796);
lean_ctor_set(x_847, 2, x_823);
lean_inc(x_847);
lean_inc(x_838);
x_848 = l_Lean_Syntax_node2(x_838, x_845, x_846, x_847);
x_849 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_838);
if (lean_is_scalar(x_840)) {
 x_850 = lean_alloc_ctor(2, 2, 0);
} else {
 x_850 = x_840;
 lean_ctor_set_tag(x_850, 2);
}
lean_ctor_set(x_850, 0, x_838);
lean_ctor_set(x_850, 1, x_849);
x_851 = lean_mk_string_unchecked("first", 5, 5);
lean_inc(x_851);
lean_inc(x_790);
lean_inc(x_789);
lean_inc(x_788);
x_852 = l_Lean_Name_mkStr4(x_788, x_789, x_790, x_851);
lean_inc(x_851);
lean_inc(x_838);
if (lean_is_scalar(x_836)) {
 x_853 = lean_alloc_ctor(2, 2, 0);
} else {
 x_853 = x_836;
 lean_ctor_set_tag(x_853, 2);
}
lean_ctor_set(x_853, 0, x_838);
lean_ctor_set(x_853, 1, x_851);
lean_inc(x_799);
lean_inc(x_838);
x_854 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_854, 0, x_838);
lean_ctor_set(x_854, 1, x_799);
lean_inc(x_796);
lean_inc(x_838);
x_855 = l_Lean_Syntax_node1(x_838, x_796, x_771);
lean_inc(x_804);
lean_inc(x_838);
x_856 = l_Lean_Syntax_node1(x_838, x_804, x_855);
lean_inc(x_802);
lean_inc(x_838);
x_857 = l_Lean_Syntax_node1(x_838, x_802, x_856);
lean_inc(x_854);
lean_inc(x_798);
lean_inc(x_838);
x_858 = l_Lean_Syntax_node2(x_838, x_798, x_854, x_857);
lean_inc(x_796);
lean_inc(x_838);
x_859 = l_Lean_Syntax_node1(x_838, x_796, x_774);
lean_inc(x_804);
lean_inc(x_838);
x_860 = l_Lean_Syntax_node1(x_838, x_804, x_859);
lean_inc(x_802);
lean_inc(x_838);
x_861 = l_Lean_Syntax_node1(x_838, x_802, x_860);
lean_inc(x_854);
lean_inc(x_798);
lean_inc(x_838);
x_862 = l_Lean_Syntax_node2(x_838, x_798, x_854, x_861);
x_863 = lean_mk_string_unchecked("exact\?", 6, 6);
lean_inc(x_863);
lean_inc(x_790);
lean_inc(x_789);
lean_inc(x_788);
x_864 = l_Lean_Name_mkStr4(x_788, x_789, x_790, x_863);
lean_inc(x_838);
x_865 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_865, 0, x_838);
lean_ctor_set(x_865, 1, x_863);
lean_inc(x_838);
x_866 = l_Lean_Syntax_node2(x_838, x_864, x_865, x_847);
lean_inc(x_796);
lean_inc(x_838);
x_867 = l_Lean_Syntax_node1(x_838, x_796, x_866);
lean_inc(x_804);
lean_inc(x_838);
x_868 = l_Lean_Syntax_node1(x_838, x_804, x_867);
lean_inc(x_802);
lean_inc(x_838);
x_869 = l_Lean_Syntax_node1(x_838, x_802, x_868);
lean_inc(x_798);
lean_inc(x_838);
x_870 = l_Lean_Syntax_node2(x_838, x_798, x_854, x_869);
lean_inc(x_796);
lean_inc(x_838);
x_871 = l_Lean_Syntax_node3(x_838, x_796, x_858, x_862, x_870);
lean_inc(x_852);
lean_inc(x_838);
x_872 = l_Lean_Syntax_node2(x_838, x_852, x_853, x_871);
lean_inc(x_796);
lean_inc(x_838);
x_873 = l_Lean_Syntax_node3(x_838, x_796, x_848, x_850, x_872);
x_874 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___lam__0(x_2, x_3, x_4, x_5, x_842);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_875 = lean_ctor_get(x_874, 0);
lean_inc(x_875);
x_876 = lean_ctor_get(x_874, 1);
lean_inc(x_876);
if (lean_is_exclusive(x_874)) {
 lean_ctor_release(x_874, 0);
 lean_ctor_release(x_874, 1);
 x_877 = x_874;
} else {
 lean_dec_ref(x_874);
 x_877 = lean_box(0);
}
x_878 = lean_st_ref_get(x_5, x_876);
lean_dec(x_5);
x_879 = lean_ctor_get(x_878, 1);
lean_inc(x_879);
if (lean_is_exclusive(x_878)) {
 lean_ctor_release(x_878, 0);
 lean_ctor_release(x_878, 1);
 x_880 = x_878;
} else {
 lean_dec_ref(x_878);
 x_880 = lean_box(0);
}
x_881 = lean_mk_string_unchecked("paren", 5, 5);
x_882 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_804);
lean_inc(x_838);
x_883 = l_Lean_Syntax_node1(x_838, x_804, x_873);
x_884 = lean_mk_string_unchecked(")", 1, 1);
x_885 = l_Lean_Name_mkStr4(x_788, x_789, x_790, x_881);
lean_inc(x_838);
if (lean_is_scalar(x_877)) {
 x_886 = lean_alloc_ctor(2, 2, 0);
} else {
 x_886 = x_877;
 lean_ctor_set_tag(x_886, 2);
}
lean_ctor_set(x_886, 0, x_838);
lean_ctor_set(x_886, 1, x_882);
lean_inc(x_802);
lean_inc(x_838);
x_887 = l_Lean_Syntax_node1(x_838, x_802, x_883);
lean_inc(x_838);
x_888 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_888, 0, x_838);
lean_ctor_set(x_888, 1, x_884);
x_889 = l_Lean_Syntax_node3(x_838, x_885, x_886, x_887, x_888);
lean_inc(x_875);
x_890 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_890, 0, x_875);
lean_ctor_set(x_890, 1, x_851);
lean_inc(x_875);
x_891 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_891, 0, x_875);
lean_ctor_set(x_891, 1, x_799);
lean_inc(x_796);
lean_inc(x_875);
x_892 = l_Lean_Syntax_node1(x_875, x_796, x_832);
lean_inc(x_804);
lean_inc(x_875);
x_893 = l_Lean_Syntax_node1(x_875, x_804, x_892);
lean_inc(x_802);
lean_inc(x_875);
x_894 = l_Lean_Syntax_node1(x_875, x_802, x_893);
lean_inc(x_891);
lean_inc(x_798);
lean_inc(x_875);
x_895 = l_Lean_Syntax_node2(x_875, x_798, x_891, x_894);
lean_inc(x_796);
lean_inc(x_875);
x_896 = l_Lean_Syntax_node1(x_875, x_796, x_834);
lean_inc(x_804);
lean_inc(x_875);
x_897 = l_Lean_Syntax_node1(x_875, x_804, x_896);
lean_inc(x_802);
lean_inc(x_875);
x_898 = l_Lean_Syntax_node1(x_875, x_802, x_897);
lean_inc(x_891);
lean_inc(x_798);
lean_inc(x_875);
x_899 = l_Lean_Syntax_node2(x_875, x_798, x_891, x_898);
lean_inc(x_796);
lean_inc(x_875);
x_900 = l_Lean_Syntax_node1(x_875, x_796, x_889);
lean_inc(x_875);
x_901 = l_Lean_Syntax_node1(x_875, x_804, x_900);
lean_inc(x_875);
x_902 = l_Lean_Syntax_node1(x_875, x_802, x_901);
lean_inc(x_875);
x_903 = l_Lean_Syntax_node2(x_875, x_798, x_891, x_902);
lean_inc(x_875);
x_904 = l_Lean_Syntax_node3(x_875, x_796, x_895, x_899, x_903);
x_905 = l_Lean_Syntax_node2(x_875, x_852, x_890, x_904);
if (lean_is_scalar(x_880)) {
 x_906 = lean_alloc_ctor(0, 2, 0);
} else {
 x_906 = x_880;
}
lean_ctor_set(x_906, 0, x_905);
lean_ctor_set(x_906, 1, x_879);
return x_906;
}
else
{
lean_dec(x_832);
lean_dec(x_823);
lean_dec(x_804);
lean_dec(x_802);
lean_dec(x_799);
lean_dec(x_798);
lean_dec(x_796);
lean_dec(x_790);
lean_dec(x_789);
lean_dec(x_788);
lean_dec(x_774);
lean_dec(x_771);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_833;
}
}
else
{
lean_dec(x_776);
lean_dec(x_774);
lean_dec(x_771);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_777;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalTryTrace___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l_Lean_Elab_Tactic_elabTryConfig___redArg(x_1, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_13);
x_18 = l_Lean_Meta_Try_Collector_main(x_16, x_13, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx(x_19, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_Tactic_Try_evalAndSuggest(x_2, x_22, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
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
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
return x_15;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_15);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_12);
if (x_37 == 0)
{
return x_12;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_12, 0);
x_39 = lean_ctor_get(x_12, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_12);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalTryTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = lean_mk_string_unchecked("tryTrace", 8, 8);
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
lean_dec(x_1);
x_23 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
lean_dec(x_1);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_evalTryTrace___lam__0___boxed), 11, 2);
lean_closure_set(x_26, 0, x_19);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 2);
lean_closure_set(x_27, 0, lean_box(0));
lean_closure_set(x_27, 1, x_26);
x_28 = l_Lean_Elab_Tactic_focus(lean_box(0), x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalTryTrace___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Try_evalTryTrace___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("tryTrace", 8, 8);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("Try", 3, 3);
x_10 = lean_mk_string_unchecked("evalTryTrace", 12, 12);
x_11 = l_Lean_Name_mkStr5(x_3, x_8, x_5, x_9, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_evalTryTrace), 10, 0);
x_13 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_11, x_12, x_1);
return x_13;
}
}
lean_object* initialize_Init_Try(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_ExposeNames(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Try(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Config(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_SimpTrace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_LibrarySearch(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Grind(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Try(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Try(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_ExposeNames(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Try(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_SimpTrace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_LibrarySearch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateTryTacticM = _init_l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateTryTacticM();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateTryTacticM);
if (builtin) {res = l_Lean_Elab_Tactic_Try_initFn____x40_Lean_Elab_Tactic_Try___hyg_4386_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_Try_tryTacticElabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_Try_tryTacticElabAttribute);
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
