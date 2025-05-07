// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Main
// Imports: Init.Grind.Lemmas Lean.Meta.Tactic.Util Lean.Meta.Tactic.ExposeNames Lean.Meta.Tactic.Simp.Diagnostics Lean.Meta.Tactic.Grind.RevertAll Lean.Meta.Tactic.Grind.PropagatorAttr Lean.Meta.Tactic.Grind.Proj Lean.Meta.Tactic.Grind.ForallProp Lean.Meta.Tactic.Grind.Util Lean.Meta.Tactic.Grind.Inv Lean.Meta.Tactic.Grind.Intro Lean.Meta.Tactic.Grind.EMatch Lean.Meta.Tactic.Grind.Split Lean.Meta.Tactic.Grind.Solve Lean.Meta.Tactic.Grind.SimpUtil Lean.Meta.Tactic.Grind.Cases
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getNatZeroExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_2570__spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getBoolFalseExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Meta_Grind_propagateForallPropDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___redArg(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___Lean_Meta_Grind_main_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Expr_lit___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkENodeCore___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getSimprocs___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_debug_terminalTacticsAsSorry;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_Meta_Grind_getFalseExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_revertAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_Match_initFn____x40_Lean_Meta_Match_MatchEqsExt___hyg_181__spec__0(lean_object*);
lean_object* l_Lean_Meta_Grind_getSimpContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__5_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Queue_empty(lean_object*);
lean_object* l_Lean_Meta_Grind_activateTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isBuiltinEagerCases(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_toGrindTactic_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___Lean_Meta_Grind_main_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_checkInvariants(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkDiagMessages(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lam__0___boxed(lean_object**);
lean_object* l_Lean_MVarId_admit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateProjEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Grind_Result_toMessageData_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getBoolTrueExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0(lean_object*);
double lean_float_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__8_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_reportIssue_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_appendTagSuffix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_betaReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Result_hasFailures(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ShareCommon_mkStateImpl(lean_object*);
lean_object* l_Lean_MessageData_ofConst(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_warningAsError;
extern lean_object* l_Lean_Meta_Grind_builtinPropagatorsRef;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clearAuxDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__14___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_goalToMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instHashableOrigin;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__4_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_ensureNoMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isDiagnosticsEnabled___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0(uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_hasFailures___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__4_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_Meta_Grind_getTrueExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Grind_Result_toMessageData_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_reportIssue_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___redArg___boxed(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitM___at___Lean_Meta_synthInstance_x3f_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_107_(uint8_t, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_List_appendTR(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateForallPropUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instBEqOrigin__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_ShareCommon_objectFactory;
lean_object* lean_state_sharecommon(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3(lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_exposeNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ppGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_Grind_getSimpContext(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_Grind_getSimprocs___redArg(x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_13);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_2570__spec__0(lean_box(0));
lean_inc(x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
lean_inc(x_15);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_17, 3, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_unsigned_to_nat(5u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_to_nat(x_21);
x_23 = lean_nat_pow(x_19, x_22);
lean_dec(x_22);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = lean_usize_to_nat(x_24);
x_26 = lean_mk_empty_array_with_capacity(x_25);
lean_dec(x_25);
lean_inc(x_26);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set_usize(x_29, 4, x_21);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_17);
lean_ctor_set(x_30, 2, x_18);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set(x_30, 4, x_8);
lean_ctor_set(x_30, 5, x_12);
lean_ctor_set(x_10, 0, x_30);
return x_10;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; lean_object* x_42; lean_object* x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_10);
x_33 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_33);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_2570__spec__0(lean_box(0));
lean_inc(x_33);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_33);
lean_inc(x_35);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_39 = lean_unsigned_to_nat(2u);
x_40 = lean_unsigned_to_nat(5u);
x_41 = lean_usize_of_nat(x_40);
x_42 = lean_usize_to_nat(x_41);
x_43 = lean_nat_pow(x_39, x_42);
lean_dec(x_42);
x_44 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_45 = lean_usize_to_nat(x_44);
x_46 = lean_mk_empty_array_with_capacity(x_45);
lean_dec(x_45);
lean_inc(x_46);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_46);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_48);
lean_ctor_set_usize(x_49, 4, x_41);
x_50 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_37);
lean_ctor_set(x_50, 2, x_38);
lean_ctor_set(x_50, 3, x_49);
lean_ctor_set(x_50, 4, x_8);
lean_ctor_set(x_50, 5, x_31);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_32);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_8);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_10);
if (x_52 == 0)
{
return x_10;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_10, 0);
x_54 = lean_ctor_get(x_10, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_10);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_mkParams(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Meta_Grind_propagateForallPropUp(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Expr_getAppFn(x_3);
switch (lean_obj_tag(x_15)) {
case 0:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Expr_bvar___override(x_16);
x_18 = lean_apply_10(x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
return x_18;
}
case 1:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = l_Lean_Expr_fvar___override(x_19);
x_21 = lean_apply_10(x_1, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
return x_21;
}
case 2:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
x_23 = l_Lean_Expr_mvar___override(x_22);
x_24 = lean_apply_10(x_1, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
return x_24;
}
case 3:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_3);
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec(x_15);
x_26 = l_Lean_Expr_sort___override(x_25);
x_27 = lean_apply_10(x_1, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
return x_27;
}
case 4:
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec(x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_29 = l_Lean_Meta_Grind_propagateProjEq(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; lean_object* x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; size_t x_45; size_t x_46; lean_object* x_47; size_t x_48; size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; 
x_31 = lean_ctor_get(x_2, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_array_get_size(x_34);
x_36 = l_Lean_Name_hash___override(x_28);
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
x_52 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(x_28, x_51);
lean_dec(x_51);
lean_dec(x_28);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_53 = lean_box(0);
lean_ctor_set(x_29, 0, x_53);
return x_29;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_free_object(x_29);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_apply_10(x_54, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint64_t x_60; lean_object* x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; lean_object* x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; size_t x_69; size_t x_70; lean_object* x_71; size_t x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; 
x_56 = lean_ctor_get(x_2, 0);
x_57 = lean_ctor_get(x_29, 1);
lean_inc(x_57);
lean_dec(x_29);
x_58 = lean_ctor_get(x_56, 1);
x_59 = lean_array_get_size(x_58);
x_60 = l_Lean_Name_hash___override(x_28);
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
x_76 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(x_28, x_75);
lean_dec(x_75);
lean_dec(x_28);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_57);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_apply_10(x_79, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_57);
return x_80;
}
}
}
else
{
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_29;
}
}
case 5:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_3);
x_81 = lean_ctor_get(x_15, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_15, 1);
lean_inc(x_82);
lean_dec(x_15);
x_83 = l_Lean_Expr_app___override(x_81, x_82);
x_84 = lean_apply_10(x_1, x_83, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
return x_84;
}
case 6:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_3);
x_85 = lean_ctor_get(x_15, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_15, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_15, 2);
lean_inc(x_87);
x_88 = lean_ctor_get_uint8(x_15, sizeof(void*)*3 + 8);
lean_dec(x_15);
x_89 = l_Lean_Expr_lam___override(x_85, x_86, x_87, x_88);
x_90 = lean_apply_10(x_1, x_89, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
return x_90;
}
case 7:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_3);
x_91 = lean_ctor_get(x_15, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_15, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_15, 2);
lean_inc(x_93);
x_94 = lean_ctor_get_uint8(x_15, sizeof(void*)*3 + 8);
lean_dec(x_15);
x_95 = l_Lean_Expr_forallE___override(x_91, x_92, x_93, x_94);
x_96 = lean_apply_10(x_1, x_95, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
return x_96;
}
case 8:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_3);
x_97 = lean_ctor_get(x_15, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_15, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_15, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_15, 3);
lean_inc(x_100);
x_101 = lean_ctor_get_uint8(x_15, sizeof(void*)*4 + 8);
lean_dec(x_15);
x_102 = l_Lean_Expr_letE___override(x_97, x_98, x_99, x_100, x_101);
x_103 = lean_apply_10(x_1, x_102, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
return x_103;
}
case 9:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_3);
x_104 = lean_ctor_get(x_15, 0);
lean_inc(x_104);
lean_dec(x_15);
x_105 = l_Lean_Expr_lit___override(x_104);
x_106 = lean_apply_10(x_1, x_105, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
return x_106;
}
case 10:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_3);
x_107 = lean_ctor_get(x_15, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_15, 1);
lean_inc(x_108);
lean_dec(x_15);
x_109 = l_Lean_Expr_mdata___override(x_107, x_108);
x_110 = lean_apply_10(x_1, x_109, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
return x_110;
}
default: 
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_3);
x_111 = lean_ctor_get(x_15, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_15, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_15, 2);
lean_inc(x_113);
lean_dec(x_15);
x_114 = l_Lean_Expr_proj___override(x_111, x_112, x_113);
x_115 = lean_apply_10(x_1, x_114, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
return x_115;
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
lean_dec(x_1);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Meta_Grind_propagateForallPropDown(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = l_Lean_Expr_getAppFn(x_3);
switch (lean_obj_tag(x_17)) {
case 0:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_13);
lean_dec(x_3);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Expr_bvar___override(x_18);
x_20 = lean_apply_10(x_1, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_20;
}
case 1:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_13);
lean_dec(x_3);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = l_Lean_Expr_fvar___override(x_21);
x_23 = lean_apply_10(x_1, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_23;
}
case 2:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_13);
lean_dec(x_3);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = l_Lean_Expr_mvar___override(x_24);
x_26 = lean_apply_10(x_1, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_26;
}
case 3:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_13);
lean_dec(x_3);
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_28 = l_Lean_Expr_sort___override(x_27);
x_29 = lean_apply_10(x_1, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_29;
}
case 4:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; size_t x_43; size_t x_44; lean_object* x_45; size_t x_46; size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_1);
x_30 = lean_ctor_get(x_2, 1);
x_31 = lean_ctor_get(x_17, 0);
lean_inc(x_31);
lean_dec(x_17);
x_32 = lean_ctor_get(x_30, 1);
x_33 = lean_array_get_size(x_32);
x_34 = l_Lean_Name_hash___override(x_31);
x_35 = lean_unsigned_to_nat(32u);
x_36 = lean_uint64_of_nat(x_35);
x_37 = lean_uint64_shift_right(x_34, x_36);
x_38 = lean_uint64_xor(x_34, x_37);
x_39 = lean_unsigned_to_nat(16u);
x_40 = lean_uint64_of_nat(x_39);
x_41 = lean_uint64_shift_right(x_38, x_40);
x_42 = lean_uint64_xor(x_38, x_41);
x_43 = lean_uint64_to_usize(x_42);
x_44 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_usize_of_nat(x_45);
x_47 = lean_usize_sub(x_44, x_46);
x_48 = lean_usize_land(x_43, x_47);
x_49 = lean_array_uget(x_32, x_48);
x_50 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(x_31, x_49);
lean_dec(x_49);
lean_dec(x_31);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = lean_box(0);
lean_ctor_set(x_13, 0, x_51);
return x_13;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_free_object(x_13);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_apply_10(x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_53;
}
}
case 5:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_free_object(x_13);
lean_dec(x_3);
x_54 = lean_ctor_get(x_17, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_17, 1);
lean_inc(x_55);
lean_dec(x_17);
x_56 = l_Lean_Expr_app___override(x_54, x_55);
x_57 = lean_apply_10(x_1, x_56, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_57;
}
case 6:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
lean_free_object(x_13);
lean_dec(x_3);
x_58 = lean_ctor_get(x_17, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_17, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_17, 2);
lean_inc(x_60);
x_61 = lean_ctor_get_uint8(x_17, sizeof(void*)*3 + 8);
lean_dec(x_17);
x_62 = l_Lean_Expr_lam___override(x_58, x_59, x_60, x_61);
x_63 = lean_apply_10(x_1, x_62, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_63;
}
case 7:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
lean_free_object(x_13);
lean_dec(x_3);
x_64 = lean_ctor_get(x_17, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_17, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_17, 2);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_17, sizeof(void*)*3 + 8);
lean_dec(x_17);
x_68 = l_Lean_Expr_forallE___override(x_64, x_65, x_66, x_67);
x_69 = lean_apply_10(x_1, x_68, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_69;
}
case 8:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
lean_free_object(x_13);
lean_dec(x_3);
x_70 = lean_ctor_get(x_17, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_17, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_17, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_17, 3);
lean_inc(x_73);
x_74 = lean_ctor_get_uint8(x_17, sizeof(void*)*4 + 8);
lean_dec(x_17);
x_75 = l_Lean_Expr_letE___override(x_70, x_71, x_72, x_73, x_74);
x_76 = lean_apply_10(x_1, x_75, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_76;
}
case 9:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_free_object(x_13);
lean_dec(x_3);
x_77 = lean_ctor_get(x_17, 0);
lean_inc(x_77);
lean_dec(x_17);
x_78 = l_Lean_Expr_lit___override(x_77);
x_79 = lean_apply_10(x_1, x_78, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_79;
}
case 10:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_free_object(x_13);
lean_dec(x_3);
x_80 = lean_ctor_get(x_17, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_17, 1);
lean_inc(x_81);
lean_dec(x_17);
x_82 = l_Lean_Expr_mdata___override(x_80, x_81);
x_83 = lean_apply_10(x_1, x_82, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_83;
}
default: 
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_free_object(x_13);
lean_dec(x_3);
x_84 = lean_ctor_get(x_17, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_17, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_17, 2);
lean_inc(x_86);
lean_dec(x_17);
x_87 = l_Lean_Expr_proj___override(x_84, x_85, x_86);
x_88 = lean_apply_10(x_1, x_87, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_13, 1);
lean_inc(x_89);
lean_dec(x_13);
x_90 = l_Lean_Expr_getAppFn(x_3);
switch (lean_obj_tag(x_90)) {
case 0:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_3);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec(x_90);
x_92 = l_Lean_Expr_bvar___override(x_91);
x_93 = lean_apply_10(x_1, x_92, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_89);
return x_93;
}
case 1:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_3);
x_94 = lean_ctor_get(x_90, 0);
lean_inc(x_94);
lean_dec(x_90);
x_95 = l_Lean_Expr_fvar___override(x_94);
x_96 = lean_apply_10(x_1, x_95, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_89);
return x_96;
}
case 2:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_3);
x_97 = lean_ctor_get(x_90, 0);
lean_inc(x_97);
lean_dec(x_90);
x_98 = l_Lean_Expr_mvar___override(x_97);
x_99 = lean_apply_10(x_1, x_98, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_89);
return x_99;
}
case 3:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_3);
x_100 = lean_ctor_get(x_90, 0);
lean_inc(x_100);
lean_dec(x_90);
x_101 = l_Lean_Expr_sort___override(x_100);
x_102 = lean_apply_10(x_1, x_101, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_89);
return x_102;
}
case 4:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint64_t x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; lean_object* x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; size_t x_116; size_t x_117; lean_object* x_118; size_t x_119; size_t x_120; size_t x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_1);
x_103 = lean_ctor_get(x_2, 1);
x_104 = lean_ctor_get(x_90, 0);
lean_inc(x_104);
lean_dec(x_90);
x_105 = lean_ctor_get(x_103, 1);
x_106 = lean_array_get_size(x_105);
x_107 = l_Lean_Name_hash___override(x_104);
x_108 = lean_unsigned_to_nat(32u);
x_109 = lean_uint64_of_nat(x_108);
x_110 = lean_uint64_shift_right(x_107, x_109);
x_111 = lean_uint64_xor(x_107, x_110);
x_112 = lean_unsigned_to_nat(16u);
x_113 = lean_uint64_of_nat(x_112);
x_114 = lean_uint64_shift_right(x_111, x_113);
x_115 = lean_uint64_xor(x_111, x_114);
x_116 = lean_uint64_to_usize(x_115);
x_117 = lean_usize_of_nat(x_106);
lean_dec(x_106);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_usize_of_nat(x_118);
x_120 = lean_usize_sub(x_117, x_119);
x_121 = lean_usize_land(x_116, x_120);
x_122 = lean_array_uget(x_105, x_121);
x_123 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(x_104, x_122);
lean_dec(x_122);
lean_dec(x_104);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_89);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_apply_10(x_126, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_89);
return x_127;
}
}
case 5:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_3);
x_128 = lean_ctor_get(x_90, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_90, 1);
lean_inc(x_129);
lean_dec(x_90);
x_130 = l_Lean_Expr_app___override(x_128, x_129);
x_131 = lean_apply_10(x_1, x_130, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_89);
return x_131;
}
case 6:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_3);
x_132 = lean_ctor_get(x_90, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_90, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_90, 2);
lean_inc(x_134);
x_135 = lean_ctor_get_uint8(x_90, sizeof(void*)*3 + 8);
lean_dec(x_90);
x_136 = l_Lean_Expr_lam___override(x_132, x_133, x_134, x_135);
x_137 = lean_apply_10(x_1, x_136, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_89);
return x_137;
}
case 7:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_3);
x_138 = lean_ctor_get(x_90, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_90, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_90, 2);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_90, sizeof(void*)*3 + 8);
lean_dec(x_90);
x_142 = l_Lean_Expr_forallE___override(x_138, x_139, x_140, x_141);
x_143 = lean_apply_10(x_1, x_142, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_89);
return x_143;
}
case 8:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_3);
x_144 = lean_ctor_get(x_90, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_90, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_90, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_90, 3);
lean_inc(x_147);
x_148 = lean_ctor_get_uint8(x_90, sizeof(void*)*4 + 8);
lean_dec(x_90);
x_149 = l_Lean_Expr_letE___override(x_144, x_145, x_146, x_147, x_148);
x_150 = lean_apply_10(x_1, x_149, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_89);
return x_150;
}
case 9:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_3);
x_151 = lean_ctor_get(x_90, 0);
lean_inc(x_151);
lean_dec(x_90);
x_152 = l_Lean_Expr_lit___override(x_151);
x_153 = lean_apply_10(x_1, x_152, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_89);
return x_153;
}
case 10:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_3);
x_154 = lean_ctor_get(x_90, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_90, 1);
lean_inc(x_155);
lean_dec(x_90);
x_156 = l_Lean_Expr_mdata___override(x_154, x_155);
x_157 = lean_apply_10(x_1, x_156, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_89);
return x_157;
}
default: 
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_3);
x_158 = lean_ctor_get(x_90, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_90, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_90, 2);
lean_inc(x_160);
lean_dec(x_90);
x_161 = l_Lean_Expr_proj___override(x_158, x_159, x_160);
x_162 = lean_apply_10(x_1, x_161, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_89);
return x_162;
}
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
lean_dec(x_1);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_Grind_builtinPropagatorsRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkMethods___redArg___lam__0___boxed), 10, 0);
lean_inc(x_6);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkMethods___redArg___lam__2___boxed), 12, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkMethods___redArg___lam__1___boxed), 12, 2);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_6);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_1);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkMethods___redArg___lam__0___boxed), 10, 0);
lean_inc(x_11);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkMethods___redArg___lam__2___boxed), 12, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_11);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkMethods___redArg___lam__1___boxed), 12, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_11);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_mkMethods___redArg(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_mkMethods___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_mkMethods___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_mkMethods___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkMethods___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_mkMethods(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_10 = l_Lean_ShareCommon_objectFactory;
x_11 = l_ShareCommon_mkStateImpl(x_10);
x_12 = lean_mk_string_unchecked("False", 5, 5);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_box(0);
x_15 = l_Lean_Expr_const___override(x_13, x_14);
x_16 = lean_state_sharecommon(x_10, x_11, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_mk_string_unchecked("True", 4, 4);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = l_Lean_Expr_const___override(x_20, x_14);
x_22 = lean_state_sharecommon(x_10, x_18, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_mk_string_unchecked("Bool", 4, 4);
x_26 = lean_mk_string_unchecked("false", 5, 5);
lean_inc(x_25);
x_27 = l_Lean_Name_mkStr2(x_25, x_26);
x_28 = l_Lean_Expr_const___override(x_27, x_14);
x_29 = lean_state_sharecommon(x_10, x_24, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_mk_string_unchecked("true", 4, 4);
x_33 = l_Lean_Name_mkStr2(x_25, x_32);
x_34 = l_Lean_Expr_const___override(x_33, x_14);
x_35 = lean_state_sharecommon(x_10, x_31, x_34);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Lean_mkNatLit(x_39);
x_41 = lean_state_sharecommon(x_10, x_38, x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = l_Lean_Meta_Grind_mkMethods___redArg(x_4, x_9);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; lean_object* x_57; lean_object* x_58; size_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; lean_object* x_83; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
x_49 = lean_unsigned_to_nat(1u);
x_50 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_50);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
lean_inc(x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_50);
lean_inc(x_52);
lean_ctor_set(x_45, 1, x_39);
lean_ctor_set(x_45, 0, x_52);
lean_inc(x_50);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_50);
x_54 = lean_unsigned_to_nat(2u);
x_55 = lean_unsigned_to_nat(5u);
x_56 = lean_usize_of_nat(x_55);
x_57 = lean_usize_to_nat(x_56);
x_58 = lean_nat_pow(x_54, x_57);
lean_dec(x_57);
x_59 = lean_usize_of_nat(x_58);
lean_dec(x_58);
x_60 = lean_usize_to_nat(x_59);
x_61 = lean_mk_empty_array_with_capacity(x_60);
lean_dec(x_60);
lean_inc(x_61);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_39);
lean_ctor_set(x_63, 3, x_39);
lean_ctor_set_usize(x_63, 4, x_56);
lean_inc(x_53);
lean_inc(x_52);
x_64 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_64, 0, x_52);
lean_ctor_set(x_64, 1, x_52);
lean_ctor_set(x_64, 2, x_53);
lean_ctor_set(x_64, 3, x_63);
lean_ctor_set(x_41, 1, x_64);
lean_ctor_set(x_41, 0, x_45);
x_65 = lean_box(0);
x_66 = lean_box(0);
x_67 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0(lean_box(0));
x_68 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Match_initFn____x40_Lean_Meta_Match_MatchEqsExt___hyg_181__spec__0(lean_box(0));
lean_inc(x_68);
x_69 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_68);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_50);
lean_ctor_set(x_35, 1, x_53);
lean_ctor_set(x_35, 0, x_70);
x_71 = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(x_71, 0, x_44);
lean_ctor_set(x_71, 1, x_49);
lean_ctor_set(x_71, 2, x_51);
lean_ctor_set(x_71, 3, x_41);
lean_ctor_set(x_71, 4, x_23);
lean_ctor_set(x_71, 5, x_17);
lean_ctor_set(x_71, 6, x_43);
lean_ctor_set(x_71, 7, x_37);
lean_ctor_set(x_71, 8, x_30);
lean_ctor_set(x_71, 9, x_65);
lean_ctor_set(x_71, 10, x_66);
lean_ctor_set(x_71, 11, x_69);
lean_ctor_set(x_71, 12, x_35);
x_72 = lean_st_mk_ref(x_71, x_48);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_3, 5);
x_76 = lean_ctor_get(x_3, 4);
x_77 = lean_ctor_get(x_3, 0);
x_78 = lean_box(0);
x_79 = lean_box(1);
lean_inc(x_77);
lean_inc(x_75);
lean_inc(x_76);
x_80 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_75);
lean_ctor_set(x_80, 2, x_2);
lean_ctor_set(x_80, 3, x_77);
x_81 = lean_unbox(x_78);
lean_ctor_set_uint8(x_80, sizeof(void*)*4, x_81);
x_82 = lean_unbox(x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*4 + 1, x_82);
lean_inc(x_73);
x_83 = lean_apply_8(x_1, x_47, x_80, x_73, x_5, x_6, x_7, x_8, x_74);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_st_ref_get(x_73, x_85);
lean_dec(x_73);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
lean_ctor_set(x_86, 0, x_84);
return x_86;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
else
{
lean_dec(x_73);
return x_83;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; size_t x_101; lean_object* x_102; lean_object* x_103; size_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_127; lean_object* x_128; 
x_91 = lean_ctor_get(x_45, 0);
x_92 = lean_ctor_get(x_45, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_45);
x_93 = lean_unsigned_to_nat(1u);
x_94 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_94);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
lean_inc(x_94);
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_94);
lean_inc(x_96);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_39);
lean_inc(x_94);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_94);
x_99 = lean_unsigned_to_nat(2u);
x_100 = lean_unsigned_to_nat(5u);
x_101 = lean_usize_of_nat(x_100);
x_102 = lean_usize_to_nat(x_101);
x_103 = lean_nat_pow(x_99, x_102);
lean_dec(x_102);
x_104 = lean_usize_of_nat(x_103);
lean_dec(x_103);
x_105 = lean_usize_to_nat(x_104);
x_106 = lean_mk_empty_array_with_capacity(x_105);
lean_dec(x_105);
lean_inc(x_106);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
lean_ctor_set(x_108, 2, x_39);
lean_ctor_set(x_108, 3, x_39);
lean_ctor_set_usize(x_108, 4, x_101);
lean_inc(x_98);
lean_inc(x_96);
x_109 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_109, 0, x_96);
lean_ctor_set(x_109, 1, x_96);
lean_ctor_set(x_109, 2, x_98);
lean_ctor_set(x_109, 3, x_108);
lean_ctor_set(x_41, 1, x_109);
lean_ctor_set(x_41, 0, x_97);
x_110 = lean_box(0);
x_111 = lean_box(0);
x_112 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0(lean_box(0));
x_113 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Match_initFn____x40_Lean_Meta_Match_MatchEqsExt___hyg_181__spec__0(lean_box(0));
lean_inc(x_113);
x_114 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_114, 2, x_113);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_94);
lean_ctor_set(x_35, 1, x_98);
lean_ctor_set(x_35, 0, x_115);
x_116 = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(x_116, 0, x_44);
lean_ctor_set(x_116, 1, x_93);
lean_ctor_set(x_116, 2, x_95);
lean_ctor_set(x_116, 3, x_41);
lean_ctor_set(x_116, 4, x_23);
lean_ctor_set(x_116, 5, x_17);
lean_ctor_set(x_116, 6, x_43);
lean_ctor_set(x_116, 7, x_37);
lean_ctor_set(x_116, 8, x_30);
lean_ctor_set(x_116, 9, x_110);
lean_ctor_set(x_116, 10, x_111);
lean_ctor_set(x_116, 11, x_114);
lean_ctor_set(x_116, 12, x_35);
x_117 = lean_st_mk_ref(x_116, x_92);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_ctor_get(x_3, 5);
x_121 = lean_ctor_get(x_3, 4);
x_122 = lean_ctor_get(x_3, 0);
x_123 = lean_box(0);
x_124 = lean_box(1);
lean_inc(x_122);
lean_inc(x_120);
lean_inc(x_121);
x_125 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_120);
lean_ctor_set(x_125, 2, x_2);
lean_ctor_set(x_125, 3, x_122);
x_126 = lean_unbox(x_123);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_126);
x_127 = lean_unbox(x_124);
lean_ctor_set_uint8(x_125, sizeof(void*)*4 + 1, x_127);
lean_inc(x_118);
x_128 = lean_apply_8(x_1, x_91, x_125, x_118, x_5, x_6, x_7, x_8, x_119);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_st_ref_get(x_118, x_130);
lean_dec(x_118);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_133 = x_131;
} else {
 lean_dec_ref(x_131);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
else
{
lean_dec(x_118);
return x_128;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; size_t x_149; lean_object* x_150; lean_object* x_151; size_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; uint8_t x_176; lean_object* x_177; 
x_135 = lean_ctor_get(x_41, 0);
x_136 = lean_ctor_get(x_41, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_41);
x_137 = l_Lean_Meta_Grind_mkMethods___redArg(x_4, x_9);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_140 = x_137;
} else {
 lean_dec_ref(x_137);
 x_140 = lean_box(0);
}
x_141 = lean_unsigned_to_nat(1u);
x_142 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_142);
x_143 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_143, 0, x_142);
lean_inc(x_142);
x_144 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_144, 0, x_142);
lean_inc(x_144);
if (lean_is_scalar(x_140)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_140;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_39);
lean_inc(x_142);
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_142);
x_147 = lean_unsigned_to_nat(2u);
x_148 = lean_unsigned_to_nat(5u);
x_149 = lean_usize_of_nat(x_148);
x_150 = lean_usize_to_nat(x_149);
x_151 = lean_nat_pow(x_147, x_150);
lean_dec(x_150);
x_152 = lean_usize_of_nat(x_151);
lean_dec(x_151);
x_153 = lean_usize_to_nat(x_152);
x_154 = lean_mk_empty_array_with_capacity(x_153);
lean_dec(x_153);
lean_inc(x_154);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
lean_ctor_set(x_156, 2, x_39);
lean_ctor_set(x_156, 3, x_39);
lean_ctor_set_usize(x_156, 4, x_149);
lean_inc(x_146);
lean_inc(x_144);
x_157 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_157, 0, x_144);
lean_ctor_set(x_157, 1, x_144);
lean_ctor_set(x_157, 2, x_146);
lean_ctor_set(x_157, 3, x_156);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_145);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_box(0);
x_160 = lean_box(0);
x_161 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0(lean_box(0));
x_162 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Match_initFn____x40_Lean_Meta_Match_MatchEqsExt___hyg_181__spec__0(lean_box(0));
lean_inc(x_162);
x_163 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
lean_ctor_set(x_163, 2, x_162);
x_164 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_164, 0, x_142);
lean_ctor_set(x_35, 1, x_146);
lean_ctor_set(x_35, 0, x_164);
x_165 = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(x_165, 0, x_136);
lean_ctor_set(x_165, 1, x_141);
lean_ctor_set(x_165, 2, x_143);
lean_ctor_set(x_165, 3, x_158);
lean_ctor_set(x_165, 4, x_23);
lean_ctor_set(x_165, 5, x_17);
lean_ctor_set(x_165, 6, x_135);
lean_ctor_set(x_165, 7, x_37);
lean_ctor_set(x_165, 8, x_30);
lean_ctor_set(x_165, 9, x_159);
lean_ctor_set(x_165, 10, x_160);
lean_ctor_set(x_165, 11, x_163);
lean_ctor_set(x_165, 12, x_35);
x_166 = lean_st_mk_ref(x_165, x_139);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_ctor_get(x_3, 5);
x_170 = lean_ctor_get(x_3, 4);
x_171 = lean_ctor_get(x_3, 0);
x_172 = lean_box(0);
x_173 = lean_box(1);
lean_inc(x_171);
lean_inc(x_169);
lean_inc(x_170);
x_174 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_174, 0, x_170);
lean_ctor_set(x_174, 1, x_169);
lean_ctor_set(x_174, 2, x_2);
lean_ctor_set(x_174, 3, x_171);
x_175 = lean_unbox(x_172);
lean_ctor_set_uint8(x_174, sizeof(void*)*4, x_175);
x_176 = lean_unbox(x_173);
lean_ctor_set_uint8(x_174, sizeof(void*)*4 + 1, x_176);
lean_inc(x_167);
x_177 = lean_apply_8(x_1, x_138, x_174, x_167, x_5, x_6, x_7, x_8, x_168);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_st_ref_get(x_167, x_179);
lean_dec(x_167);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_182 = x_180;
} else {
 lean_dec_ref(x_180);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_178);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
else
{
lean_dec(x_167);
return x_177;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; size_t x_204; lean_object* x_205; lean_object* x_206; size_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; uint8_t x_232; lean_object* x_233; 
x_184 = lean_ctor_get(x_35, 0);
x_185 = lean_ctor_get(x_35, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_35);
x_186 = lean_unsigned_to_nat(0u);
x_187 = l_Lean_mkNatLit(x_186);
x_188 = lean_state_sharecommon(x_10, x_185, x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_191 = x_188;
} else {
 lean_dec_ref(x_188);
 x_191 = lean_box(0);
}
x_192 = l_Lean_Meta_Grind_mkMethods___redArg(x_4, x_9);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_195 = x_192;
} else {
 lean_dec_ref(x_192);
 x_195 = lean_box(0);
}
x_196 = lean_unsigned_to_nat(1u);
x_197 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_197);
x_198 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_198, 0, x_197);
lean_inc(x_197);
x_199 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_199, 0, x_197);
lean_inc(x_199);
if (lean_is_scalar(x_195)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_195;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_186);
lean_inc(x_197);
x_201 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_201, 0, x_197);
x_202 = lean_unsigned_to_nat(2u);
x_203 = lean_unsigned_to_nat(5u);
x_204 = lean_usize_of_nat(x_203);
x_205 = lean_usize_to_nat(x_204);
x_206 = lean_nat_pow(x_202, x_205);
lean_dec(x_205);
x_207 = lean_usize_of_nat(x_206);
lean_dec(x_206);
x_208 = lean_usize_to_nat(x_207);
x_209 = lean_mk_empty_array_with_capacity(x_208);
lean_dec(x_208);
lean_inc(x_209);
x_210 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_210, 0, x_209);
x_211 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_209);
lean_ctor_set(x_211, 2, x_186);
lean_ctor_set(x_211, 3, x_186);
lean_ctor_set_usize(x_211, 4, x_204);
lean_inc(x_201);
lean_inc(x_199);
x_212 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_212, 0, x_199);
lean_ctor_set(x_212, 1, x_199);
lean_ctor_set(x_212, 2, x_201);
lean_ctor_set(x_212, 3, x_211);
if (lean_is_scalar(x_191)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_191;
}
lean_ctor_set(x_213, 0, x_200);
lean_ctor_set(x_213, 1, x_212);
x_214 = lean_box(0);
x_215 = lean_box(0);
x_216 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0(lean_box(0));
x_217 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Match_initFn____x40_Lean_Meta_Match_MatchEqsExt___hyg_181__spec__0(lean_box(0));
lean_inc(x_217);
x_218 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set(x_218, 2, x_217);
x_219 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_219, 0, x_197);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_201);
x_221 = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(x_221, 0, x_190);
lean_ctor_set(x_221, 1, x_196);
lean_ctor_set(x_221, 2, x_198);
lean_ctor_set(x_221, 3, x_213);
lean_ctor_set(x_221, 4, x_23);
lean_ctor_set(x_221, 5, x_17);
lean_ctor_set(x_221, 6, x_189);
lean_ctor_set(x_221, 7, x_184);
lean_ctor_set(x_221, 8, x_30);
lean_ctor_set(x_221, 9, x_214);
lean_ctor_set(x_221, 10, x_215);
lean_ctor_set(x_221, 11, x_218);
lean_ctor_set(x_221, 12, x_220);
x_222 = lean_st_mk_ref(x_221, x_194);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_ctor_get(x_3, 5);
x_226 = lean_ctor_get(x_3, 4);
x_227 = lean_ctor_get(x_3, 0);
x_228 = lean_box(0);
x_229 = lean_box(1);
lean_inc(x_227);
lean_inc(x_225);
lean_inc(x_226);
x_230 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_230, 0, x_226);
lean_ctor_set(x_230, 1, x_225);
lean_ctor_set(x_230, 2, x_2);
lean_ctor_set(x_230, 3, x_227);
x_231 = lean_unbox(x_228);
lean_ctor_set_uint8(x_230, sizeof(void*)*4, x_231);
x_232 = lean_unbox(x_229);
lean_ctor_set_uint8(x_230, sizeof(void*)*4 + 1, x_232);
lean_inc(x_223);
x_233 = lean_apply_8(x_1, x_193, x_230, x_223, x_5, x_6, x_7, x_8, x_224);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_st_ref_get(x_223, x_235);
lean_dec(x_223);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_238 = x_236;
} else {
 lean_dec_ref(x_236);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_234);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
else
{
lean_dec(x_223);
return x_233;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_GrindM_run___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_GrindM_run___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_GrindM_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_GrindM_run(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_uget(x_2, x_4);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
lean_inc(x_14);
x_15 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0(x_1, x_13, x_14, x_6, x_7, x_8, x_9, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
lean_dec(x_14);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_usize_of_nat(x_29);
x_31 = lean_usize_add(x_4, x_30);
x_4 = x_31;
x_5 = x_28;
x_10 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_box(0);
x_17 = lean_array_uget(x_1, x_3);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_dec(x_4);
if (lean_obj_tag(x_17) == 0)
{
x_9 = x_18;
x_10 = x_5;
goto block_16;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_23, 2);
lean_inc(x_24);
lean_dec(x_23);
x_19 = x_24;
goto block_22;
}
block_16:
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_4 = x_11;
x_5 = x_10;
goto _start;
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_18, x_19, x_20);
x_9 = x_21;
x_10 = x_5;
goto block_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_box(0);
x_21 = lean_array_uget(x_1, x_3);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_dec(x_4);
if (lean_obj_tag(x_21) == 0)
{
x_13 = x_22;
x_14 = x_9;
goto block_20;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_ctor_get(x_27, 2);
lean_inc(x_28);
lean_dec(x_27);
x_23 = x_28;
goto block_26;
}
block_20:
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_3, x_17);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_18, x_15, x_14);
return x_19;
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_22, x_23, x_24);
x_13 = x_25;
x_14 = x_9;
goto block_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
x_13 = lean_array_size(x_10);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_usize_of_nat(x_14);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__0(x_1, x_10, x_13, x_15, x_12, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_21);
lean_ctor_set(x_16, 0, x_2);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_17);
lean_free_object(x_2);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_16, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_27);
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_ctor_get(x_18, 0);
lean_inc(x_29);
lean_dec(x_18);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; lean_object* x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
lean_dec(x_2);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_3);
x_34 = lean_array_size(x_31);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_usize_of_nat(x_35);
x_37 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__0(x_1, x_31, x_34, x_36, x_33, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_31);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_41 = x_37;
} else {
 lean_dec_ref(x_37);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_38);
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_46 = x_37;
} else {
 lean_dec_ref(x_37);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_39, 0);
lean_inc(x_47);
lean_dec(x_39);
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
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_2);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; lean_object* x_54; size_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_2, 0);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_3);
x_53 = lean_array_size(x_50);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_usize_of_nat(x_54);
x_56 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1(x_50, x_53, x_55, x_52, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_50);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_56, 0);
lean_dec(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec(x_57);
lean_ctor_set(x_2, 0, x_61);
lean_ctor_set(x_56, 0, x_2);
return x_56;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
lean_dec(x_56);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_dec(x_57);
lean_ctor_set(x_2, 0, x_63);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_2);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_57);
lean_free_object(x_2);
x_65 = !lean_is_exclusive(x_56);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_56, 0);
lean_dec(x_66);
x_67 = lean_ctor_get(x_58, 0);
lean_inc(x_67);
lean_dec(x_58);
lean_ctor_set(x_56, 0, x_67);
return x_56;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_56, 1);
lean_inc(x_68);
lean_dec(x_56);
x_69 = lean_ctor_get(x_58, 0);
lean_inc(x_69);
lean_dec(x_58);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; size_t x_74; lean_object* x_75; size_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_71 = lean_ctor_get(x_2, 0);
lean_inc(x_71);
lean_dec(x_2);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_3);
x_74 = lean_array_size(x_71);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_usize_of_nat(x_75);
x_77 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1(x_71, x_74, x_76, x_73, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_71);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_81 = x_77;
} else {
 lean_dec_ref(x_77);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_dec(x_78);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
if (lean_is_scalar(x_81)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_81;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_78);
x_85 = lean_ctor_get(x_77, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_86 = x_77;
} else {
 lean_dec_ref(x_77);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_79, 0);
lean_inc(x_87);
lean_dec(x_79);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__4_spec__4___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_box(0);
x_17 = lean_array_uget(x_1, x_3);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_dec(x_4);
if (lean_obj_tag(x_17) == 0)
{
x_9 = x_18;
x_10 = x_5;
goto block_16;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_23, 2);
lean_inc(x_24);
lean_dec(x_23);
x_19 = x_24;
goto block_22;
}
block_16:
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_4 = x_11;
x_5 = x_10;
goto _start;
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_18, x_19, x_20);
x_9 = x_21;
x_10 = x_5;
goto block_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__4_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__4_spec__4___redArg(x_1, x_2, x_3, x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_box(0);
x_21 = lean_array_uget(x_1, x_3);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_dec(x_4);
if (lean_obj_tag(x_21) == 0)
{
x_13 = x_22;
x_14 = x_9;
goto block_20;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_ctor_get(x_27, 2);
lean_inc(x_28);
lean_dec(x_27);
x_23 = x_28;
goto block_26;
}
block_20:
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_3, x_17);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__4_spec__4___redArg(x_1, x_2, x_18, x_15, x_14);
return x_19;
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_22, x_23, x_24);
x_13 = x_25;
x_14 = x_9;
goto block_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_inc(x_2);
x_9 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0(x_2, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_array_size(x_19);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_usize_of_nat(x_23);
x_25 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__4(x_19, x_22, x_24, x_21, x_3, x_4, x_5, x_6, x_17);
lean_dec(x_19);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_26);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_25, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_36);
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_dec(x_25);
x_38 = lean_ctor_get(x_27, 0);
lean_inc(x_38);
lean_dec(x_27);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (x_1 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_7 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Match_initFn____x40_Lean_Meta_Match_MatchEqsExt___hyg_181__spec__0(lean_box(0));
x_8 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Match_initFn____x40_Lean_Meta_Match_MatchEqsExt___hyg_181__spec__0(lean_box(0));
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0(x_14, x_12, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 11);
x_10 = lean_box(x_9);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___boxed), 6, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1_spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0_spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__4_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__4_spec__4___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__4_spec__4(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0_spec__4(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___lam__0(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_4, x_3);
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
lean_dec(x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_array_uget(x_2, x_4);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_dec(x_5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_18);
x_19 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4(x_1, x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_20);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
lean_dec(x_18);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_usize_of_nat(x_33);
x_35 = lean_usize_add(x_4, x_34);
x_4 = x_35;
x_5 = x_32;
x_14 = x_29;
goto _start;
}
}
else
{
uint8_t x_37; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_37 = !lean_is_exclusive(x_19);
if (x_37 == 0)
{
return x_19;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_19, 0);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_19);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__5_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
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
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uget(x_1, x_3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_Meta_Grind_activateTheorem(x_17, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_add(x_3, x_24);
x_3 = x_25;
x_4 = x_22;
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
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
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
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uget(x_1, x_3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_Meta_Grind_activateTheorem(x_17, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_add(x_3, x_24);
x_26 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__5_spec__5(x_1, x_2, x_25, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
return x_26;
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
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; size_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
x_17 = lean_array_size(x_14);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_usize_of_nat(x_18);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__4(x_1, x_14, x_17, x_19, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_25);
lean_ctor_set(x_20, 0, x_2);
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_21);
lean_free_object(x_2);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_20, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_31);
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_ctor_get(x_22, 0);
lean_inc(x_33);
lean_dec(x_22);
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
lean_free_object(x_2);
x_35 = !lean_is_exclusive(x_20);
if (x_35 == 0)
{
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_20);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; lean_object* x_43; size_t x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_2, 0);
lean_inc(x_39);
lean_dec(x_2);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_3);
x_42 = lean_array_size(x_39);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_usize_of_nat(x_43);
x_45 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__4(x_1, x_39, x_42, x_44, x_41, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_39);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_49 = x_45;
} else {
 lean_dec_ref(x_45);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_46);
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_54 = x_45;
} else {
 lean_dec_ref(x_45);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
lean_dec(x_47);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_45, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_59 = x_45;
} else {
 lean_dec_ref(x_45);
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
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_2);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; lean_object* x_66; size_t x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_2, 0);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_3);
x_65 = lean_array_size(x_62);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_usize_of_nat(x_66);
x_68 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__5(x_62, x_65, x_67, x_64, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_62);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_68, 0);
lean_dec(x_72);
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_dec(x_69);
lean_ctor_set(x_2, 0, x_73);
lean_ctor_set(x_68, 0, x_2);
return x_68;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
lean_dec(x_68);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
lean_dec(x_69);
lean_ctor_set(x_2, 0, x_75);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_2);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_69);
lean_free_object(x_2);
x_77 = !lean_is_exclusive(x_68);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_68, 0);
lean_dec(x_78);
x_79 = lean_ctor_get(x_70, 0);
lean_inc(x_79);
lean_dec(x_70);
lean_ctor_set(x_68, 0, x_79);
return x_68;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_68, 1);
lean_inc(x_80);
lean_dec(x_68);
x_81 = lean_ctor_get(x_70, 0);
lean_inc(x_81);
lean_dec(x_70);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_free_object(x_2);
x_83 = !lean_is_exclusive(x_68);
if (x_83 == 0)
{
return x_68;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_68, 0);
x_85 = lean_ctor_get(x_68, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_68);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; size_t x_90; lean_object* x_91; size_t x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_2, 0);
lean_inc(x_87);
lean_dec(x_2);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_3);
x_90 = lean_array_size(x_87);
x_91 = lean_unsigned_to_nat(0u);
x_92 = lean_usize_of_nat(x_91);
x_93 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__5(x_87, x_90, x_92, x_89, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_87);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_97 = x_93;
} else {
 lean_dec_ref(x_93);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
if (lean_is_scalar(x_97)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_97;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_96);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_94);
x_101 = lean_ctor_get(x_93, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_102 = x_93;
} else {
 lean_dec_ref(x_93);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_95, 0);
lean_inc(x_103);
lean_dec(x_95);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_93, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_93, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_107 = x_93;
} else {
 lean_dec_ref(x_93);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__8_spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
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
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uget(x_1, x_3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_Meta_Grind_activateTheorem(x_17, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_add(x_3, x_24);
x_3 = x_25;
x_4 = x_22;
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
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
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
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uget(x_1, x_3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_Meta_Grind_activateTheorem(x_17, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_add(x_3, x_24);
x_26 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__8_spec__8(x_1, x_2, x_25, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
return x_26;
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
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4(x_2, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; size_t x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_array_size(x_23);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_usize_of_nat(x_27);
x_29 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__8(x_23, x_26, x_28, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_23);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_30);
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
}
else
{
uint8_t x_48; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_13);
if (x_48 == 0)
{
return x_13;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_13, 0);
x_50 = lean_ctor_get(x_13, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_13);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_19 = lean_st_mk_ref(x_1, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_5);
x_32 = l_Lean_Meta_Grind_mkENodeCore___redArg(x_2, x_3, x_4, x_5, x_20, x_21);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_5);
x_34 = l_Lean_Meta_Grind_mkENodeCore___redArg(x_6, x_3, x_4, x_5, x_20, x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_5);
x_36 = l_Lean_Meta_Grind_mkENodeCore___redArg(x_7, x_4, x_3, x_5, x_20, x_35);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_5);
x_38 = l_Lean_Meta_Grind_mkENodeCore___redArg(x_8, x_4, x_3, x_5, x_20, x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Meta_Grind_mkENodeCore___redArg(x_9, x_3, x_4, x_5, x_20, x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get(x_10, 3);
lean_inc(x_42);
lean_dec(x_10);
x_43 = lean_box(0);
lean_inc(x_20);
x_44 = l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4(x_42, x_43, x_20, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_41);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_22 = x_45;
goto block_31;
}
else
{
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_22 = x_46;
goto block_31;
}
else
{
uint8_t x_47; 
lean_dec(x_20);
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
block_31:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_st_ref_get(x_20, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_20, x_25);
lean_dec(x_20);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_316; uint8_t x_317; 
x_316 = lean_ctor_get(x_2, 0);
lean_inc(x_316);
x_317 = lean_ctor_get_uint8(x_316, sizeof(void*)*7 + 11);
lean_dec(x_316);
if (x_317 == 0)
{
x_11 = x_1;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
goto block_315;
}
else
{
lean_object* x_318; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_318 = l_Lean_MVarId_exposeNames(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
x_11 = x_319;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_320;
goto block_315;
}
else
{
uint8_t x_321; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_321 = !lean_is_exclusive(x_318);
if (x_321 == 0)
{
return x_318;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_318, 0);
x_323 = lean_ctor_get(x_318, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_318);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
return x_324;
}
}
}
block_315:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_20 = l_Lean_Meta_Grind_getTrueExpr(x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_Grind_getFalseExpr(x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_Grind_getBoolTrueExpr___redArg(x_14, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_Grind_getBoolFalseExpr___redArg(x_14, x_28);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = l_Lean_Meta_Grind_getNatZeroExpr___redArg(x_14, x_32);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_11);
x_37 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState(x_11, x_2, x_15, x_16, x_17, x_18, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; lean_object* x_50; lean_object* x_51; size_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 2);
lean_inc(x_41);
x_42 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_42);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_inc(x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_42);
lean_inc(x_44);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_44);
lean_inc(x_42);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_42);
x_47 = lean_unsigned_to_nat(2u);
x_48 = lean_unsigned_to_nat(5u);
x_49 = lean_usize_of_nat(x_48);
x_50 = lean_usize_to_nat(x_49);
x_51 = lean_nat_pow(x_47, x_50);
lean_dec(x_50);
x_52 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_mk_empty_array_with_capacity(x_53);
lean_dec(x_53);
lean_inc(x_54);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_unsigned_to_nat(0u);
lean_inc(x_54);
x_57 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_57, 3, x_56);
lean_ctor_set_usize(x_57, 4, x_49);
lean_inc(x_42);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_42);
x_59 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0(lean_box(0));
lean_inc(x_42);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_42);
x_61 = lean_mk_empty_array_with_capacity(x_56);
x_62 = lean_box(0);
x_63 = l_Std_Queue_empty(lean_box(0));
lean_inc(x_42);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_42);
lean_inc(x_54);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_54);
lean_inc(x_54);
x_66 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_54);
lean_ctor_set(x_66, 2, x_56);
lean_ctor_set(x_66, 3, x_56);
lean_ctor_set_usize(x_66, 4, x_49);
x_67 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__1(lean_box(0));
x_68 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Match_initFn____x40_Lean_Meta_Match_MatchEqsExt___hyg_181__spec__0(lean_box(0));
lean_inc(x_66);
x_69 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_69, 0, x_40);
lean_ctor_set(x_69, 1, x_56);
lean_ctor_set(x_69, 2, x_66);
lean_ctor_set(x_69, 3, x_66);
lean_ctor_set(x_69, 4, x_56);
lean_ctor_set(x_69, 5, x_56);
lean_ctor_set(x_69, 6, x_67);
lean_ctor_set(x_69, 7, x_56);
lean_ctor_set(x_69, 8, x_68);
x_70 = lean_box(0);
x_71 = lean_unsigned_to_nat(8u);
x_72 = lean_nat_shiftl(x_71, x_47);
x_73 = lean_unsigned_to_nat(3u);
x_74 = lean_nat_div(x_72, x_73);
lean_dec(x_72);
x_75 = l_Nat_nextPowerOfTwo(x_74);
lean_dec(x_74);
x_76 = lean_box(0);
lean_inc(x_75);
x_77 = lean_mk_array(x_75, x_76);
lean_ctor_set(x_33, 1, x_77);
lean_ctor_set(x_33, 0, x_56);
x_78 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__2(lean_box(0));
x_79 = lean_box(0);
x_80 = lean_box(0);
x_81 = lean_mk_array(x_75, x_80);
lean_ctor_set(x_29, 1, x_81);
lean_ctor_set(x_29, 0, x_56);
lean_inc(x_42);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_42);
x_83 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_83, 0, x_56);
lean_ctor_set(x_83, 1, x_41);
lean_ctor_set(x_83, 2, x_70);
lean_ctor_set(x_83, 3, x_33);
lean_ctor_set(x_83, 4, x_78);
lean_ctor_set(x_83, 5, x_79);
lean_ctor_set(x_83, 6, x_70);
lean_ctor_set(x_83, 7, x_29);
lean_ctor_set(x_83, 8, x_82);
lean_inc(x_42);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_42);
lean_inc(x_42);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_42);
lean_inc(x_42);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_42);
lean_inc(x_54);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_54);
lean_inc(x_54);
x_88 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_54);
lean_ctor_set(x_88, 2, x_56);
lean_ctor_set(x_88, 3, x_56);
lean_ctor_set_usize(x_88, 4, x_49);
lean_inc(x_54);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_54);
lean_inc(x_54);
x_90 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_54);
lean_ctor_set(x_90, 2, x_56);
lean_ctor_set(x_90, 3, x_56);
lean_ctor_set_usize(x_90, 4, x_49);
x_91 = lean_box(0);
lean_inc(x_88);
lean_inc(x_84);
lean_inc(x_57);
x_92 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_92, 0, x_57);
lean_ctor_set(x_92, 1, x_84);
lean_ctor_set(x_92, 2, x_85);
lean_ctor_set(x_92, 3, x_86);
lean_ctor_set(x_92, 4, x_88);
lean_ctor_set(x_92, 5, x_88);
lean_ctor_set(x_92, 6, x_90);
lean_ctor_set(x_92, 7, x_91);
lean_inc(x_42);
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_42);
lean_inc(x_42);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_42);
lean_inc(x_54);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_54);
lean_inc(x_54);
x_96 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_54);
lean_ctor_set(x_96, 2, x_56);
lean_ctor_set(x_96, 3, x_56);
lean_ctor_set_usize(x_96, 4, x_49);
lean_inc(x_54);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_54);
lean_inc(x_54);
x_98 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_54);
lean_ctor_set(x_98, 2, x_56);
lean_ctor_set(x_98, 3, x_56);
lean_ctor_set_usize(x_98, 4, x_49);
lean_inc(x_54);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_54);
lean_inc(x_54);
x_100 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_54);
lean_ctor_set(x_100, 2, x_56);
lean_ctor_set(x_100, 3, x_56);
lean_ctor_set_usize(x_100, 4, x_49);
lean_inc(x_54);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_54);
lean_inc(x_54);
x_102 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_54);
lean_ctor_set(x_102, 2, x_56);
lean_ctor_set(x_102, 3, x_56);
lean_ctor_set_usize(x_102, 4, x_49);
x_103 = lean_box(0);
lean_inc(x_54);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_54);
lean_inc(x_54);
x_105 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_54);
lean_ctor_set(x_105, 2, x_56);
lean_ctor_set(x_105, 3, x_56);
lean_ctor_set_usize(x_105, 4, x_49);
lean_inc(x_54);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_54);
x_107 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_54);
lean_ctor_set(x_107, 2, x_56);
lean_ctor_set(x_107, 3, x_56);
lean_ctor_set_usize(x_107, 4, x_49);
x_108 = lean_box(0);
lean_inc(x_42);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_42);
x_110 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3(lean_box(0));
lean_inc(x_98);
lean_inc_n(x_84, 2);
lean_inc(x_57);
x_111 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_111, 0, x_57);
lean_ctor_set(x_111, 1, x_84);
lean_ctor_set(x_111, 2, x_93);
lean_ctor_set(x_111, 3, x_94);
lean_ctor_set(x_111, 4, x_84);
lean_ctor_set(x_111, 5, x_96);
lean_ctor_set(x_111, 6, x_98);
lean_ctor_set(x_111, 7, x_98);
lean_ctor_set(x_111, 8, x_100);
lean_ctor_set(x_111, 9, x_102);
lean_ctor_set(x_111, 10, x_103);
lean_ctor_set(x_111, 11, x_105);
lean_ctor_set(x_111, 12, x_107);
lean_ctor_set(x_111, 13, x_56);
lean_ctor_set(x_111, 14, x_108);
lean_ctor_set(x_111, 15, x_109);
lean_ctor_set(x_111, 16, x_110);
x_112 = lean_unbox(x_62);
lean_ctor_set_uint8(x_111, sizeof(void*)*17, x_112);
x_113 = l_Array_empty(lean_box(0));
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_42);
x_115 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_115, 2, x_84);
lean_ctor_set(x_115, 3, x_56);
x_116 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_116, 0, x_92);
lean_ctor_set(x_116, 1, x_111);
lean_ctor_set(x_116, 2, x_115);
lean_inc(x_57);
lean_inc(x_11);
x_117 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_117, 0, x_11);
lean_ctor_set(x_117, 1, x_45);
lean_ctor_set(x_117, 2, x_46);
lean_ctor_set(x_117, 3, x_57);
lean_ctor_set(x_117, 4, x_58);
lean_ctor_set(x_117, 5, x_59);
lean_ctor_set(x_117, 6, x_60);
lean_ctor_set(x_117, 7, x_61);
lean_ctor_set(x_117, 8, x_56);
lean_ctor_set(x_117, 9, x_63);
lean_ctor_set(x_117, 10, x_57);
lean_ctor_set(x_117, 11, x_64);
lean_ctor_set(x_117, 12, x_69);
lean_ctor_set(x_117, 13, x_83);
lean_ctor_set(x_117, 14, x_116);
lean_ctor_set(x_117, 15, x_38);
x_118 = lean_unbox(x_62);
lean_ctor_set_uint8(x_117, sizeof(void*)*16, x_118);
x_119 = lean_box(1);
x_120 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lam__0___boxed), 18, 10);
lean_closure_set(x_120, 0, x_117);
lean_closure_set(x_120, 1, x_24);
lean_closure_set(x_120, 2, x_119);
lean_closure_set(x_120, 3, x_62);
lean_closure_set(x_120, 4, x_56);
lean_closure_set(x_120, 5, x_21);
lean_closure_set(x_120, 6, x_27);
lean_closure_set(x_120, 7, x_31);
lean_closure_set(x_120, 8, x_35);
lean_closure_set(x_120, 9, x_2);
x_121 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_toGrindTactic_spec__0___redArg(x_11, x_120, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_39);
return x_121;
}
else
{
uint8_t x_122; 
lean_free_object(x_33);
lean_dec(x_35);
lean_free_object(x_29);
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_37);
if (x_122 == 0)
{
return x_37;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_37, 0);
x_124 = lean_ctor_get(x_37, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_37);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_33, 0);
x_127 = lean_ctor_get(x_33, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_33);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_11);
x_128 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState(x_11, x_2, x_15, x_16, x_17, x_18, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; size_t x_140; lean_object* x_141; lean_object* x_142; size_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_ctor_get(x_2, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_2, 2);
lean_inc(x_132);
x_133 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_133);
x_134 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_134, 0, x_133);
lean_inc(x_133);
x_135 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_135, 0, x_133);
lean_inc(x_135);
x_136 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_136, 2, x_135);
lean_inc(x_133);
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_133);
x_138 = lean_unsigned_to_nat(2u);
x_139 = lean_unsigned_to_nat(5u);
x_140 = lean_usize_of_nat(x_139);
x_141 = lean_usize_to_nat(x_140);
x_142 = lean_nat_pow(x_138, x_141);
lean_dec(x_141);
x_143 = lean_usize_of_nat(x_142);
lean_dec(x_142);
x_144 = lean_usize_to_nat(x_143);
x_145 = lean_mk_empty_array_with_capacity(x_144);
lean_dec(x_144);
lean_inc(x_145);
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = lean_unsigned_to_nat(0u);
lean_inc(x_145);
x_148 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_145);
lean_ctor_set(x_148, 2, x_147);
lean_ctor_set(x_148, 3, x_147);
lean_ctor_set_usize(x_148, 4, x_140);
lean_inc(x_133);
x_149 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_149, 0, x_133);
x_150 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0(lean_box(0));
lean_inc(x_133);
x_151 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_151, 0, x_133);
x_152 = lean_mk_empty_array_with_capacity(x_147);
x_153 = lean_box(0);
x_154 = l_Std_Queue_empty(lean_box(0));
lean_inc(x_133);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_133);
lean_inc(x_145);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_145);
lean_inc(x_145);
x_157 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_145);
lean_ctor_set(x_157, 2, x_147);
lean_ctor_set(x_157, 3, x_147);
lean_ctor_set_usize(x_157, 4, x_140);
x_158 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__1(lean_box(0));
x_159 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Match_initFn____x40_Lean_Meta_Match_MatchEqsExt___hyg_181__spec__0(lean_box(0));
lean_inc(x_157);
x_160 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_160, 0, x_131);
lean_ctor_set(x_160, 1, x_147);
lean_ctor_set(x_160, 2, x_157);
lean_ctor_set(x_160, 3, x_157);
lean_ctor_set(x_160, 4, x_147);
lean_ctor_set(x_160, 5, x_147);
lean_ctor_set(x_160, 6, x_158);
lean_ctor_set(x_160, 7, x_147);
lean_ctor_set(x_160, 8, x_159);
x_161 = lean_box(0);
x_162 = lean_unsigned_to_nat(8u);
x_163 = lean_nat_shiftl(x_162, x_138);
x_164 = lean_unsigned_to_nat(3u);
x_165 = lean_nat_div(x_163, x_164);
lean_dec(x_163);
x_166 = l_Nat_nextPowerOfTwo(x_165);
lean_dec(x_165);
x_167 = lean_box(0);
lean_inc(x_166);
x_168 = lean_mk_array(x_166, x_167);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_147);
lean_ctor_set(x_169, 1, x_168);
x_170 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__2(lean_box(0));
x_171 = lean_box(0);
x_172 = lean_box(0);
x_173 = lean_mk_array(x_166, x_172);
lean_ctor_set(x_29, 1, x_173);
lean_ctor_set(x_29, 0, x_147);
lean_inc(x_133);
x_174 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_174, 0, x_133);
x_175 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_175, 0, x_147);
lean_ctor_set(x_175, 1, x_132);
lean_ctor_set(x_175, 2, x_161);
lean_ctor_set(x_175, 3, x_169);
lean_ctor_set(x_175, 4, x_170);
lean_ctor_set(x_175, 5, x_171);
lean_ctor_set(x_175, 6, x_161);
lean_ctor_set(x_175, 7, x_29);
lean_ctor_set(x_175, 8, x_174);
lean_inc(x_133);
x_176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_176, 0, x_133);
lean_inc(x_133);
x_177 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_177, 0, x_133);
lean_inc(x_133);
x_178 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_178, 0, x_133);
lean_inc(x_145);
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_145);
lean_inc(x_145);
x_180 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_145);
lean_ctor_set(x_180, 2, x_147);
lean_ctor_set(x_180, 3, x_147);
lean_ctor_set_usize(x_180, 4, x_140);
lean_inc(x_145);
x_181 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_181, 0, x_145);
lean_inc(x_145);
x_182 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_145);
lean_ctor_set(x_182, 2, x_147);
lean_ctor_set(x_182, 3, x_147);
lean_ctor_set_usize(x_182, 4, x_140);
x_183 = lean_box(0);
lean_inc(x_180);
lean_inc(x_176);
lean_inc(x_148);
x_184 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_184, 0, x_148);
lean_ctor_set(x_184, 1, x_176);
lean_ctor_set(x_184, 2, x_177);
lean_ctor_set(x_184, 3, x_178);
lean_ctor_set(x_184, 4, x_180);
lean_ctor_set(x_184, 5, x_180);
lean_ctor_set(x_184, 6, x_182);
lean_ctor_set(x_184, 7, x_183);
lean_inc(x_133);
x_185 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_185, 0, x_133);
lean_inc(x_133);
x_186 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_186, 0, x_133);
lean_inc(x_145);
x_187 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_187, 0, x_145);
lean_inc(x_145);
x_188 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_145);
lean_ctor_set(x_188, 2, x_147);
lean_ctor_set(x_188, 3, x_147);
lean_ctor_set_usize(x_188, 4, x_140);
lean_inc(x_145);
x_189 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_189, 0, x_145);
lean_inc(x_145);
x_190 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_145);
lean_ctor_set(x_190, 2, x_147);
lean_ctor_set(x_190, 3, x_147);
lean_ctor_set_usize(x_190, 4, x_140);
lean_inc(x_145);
x_191 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_191, 0, x_145);
lean_inc(x_145);
x_192 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_145);
lean_ctor_set(x_192, 2, x_147);
lean_ctor_set(x_192, 3, x_147);
lean_ctor_set_usize(x_192, 4, x_140);
lean_inc(x_145);
x_193 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_193, 0, x_145);
lean_inc(x_145);
x_194 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_145);
lean_ctor_set(x_194, 2, x_147);
lean_ctor_set(x_194, 3, x_147);
lean_ctor_set_usize(x_194, 4, x_140);
x_195 = lean_box(0);
lean_inc(x_145);
x_196 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_196, 0, x_145);
lean_inc(x_145);
x_197 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_145);
lean_ctor_set(x_197, 2, x_147);
lean_ctor_set(x_197, 3, x_147);
lean_ctor_set_usize(x_197, 4, x_140);
lean_inc(x_145);
x_198 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_198, 0, x_145);
x_199 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_145);
lean_ctor_set(x_199, 2, x_147);
lean_ctor_set(x_199, 3, x_147);
lean_ctor_set_usize(x_199, 4, x_140);
x_200 = lean_box(0);
lean_inc(x_133);
x_201 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_201, 0, x_133);
x_202 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3(lean_box(0));
lean_inc(x_190);
lean_inc_n(x_176, 2);
lean_inc(x_148);
x_203 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_203, 0, x_148);
lean_ctor_set(x_203, 1, x_176);
lean_ctor_set(x_203, 2, x_185);
lean_ctor_set(x_203, 3, x_186);
lean_ctor_set(x_203, 4, x_176);
lean_ctor_set(x_203, 5, x_188);
lean_ctor_set(x_203, 6, x_190);
lean_ctor_set(x_203, 7, x_190);
lean_ctor_set(x_203, 8, x_192);
lean_ctor_set(x_203, 9, x_194);
lean_ctor_set(x_203, 10, x_195);
lean_ctor_set(x_203, 11, x_197);
lean_ctor_set(x_203, 12, x_199);
lean_ctor_set(x_203, 13, x_147);
lean_ctor_set(x_203, 14, x_200);
lean_ctor_set(x_203, 15, x_201);
lean_ctor_set(x_203, 16, x_202);
x_204 = lean_unbox(x_153);
lean_ctor_set_uint8(x_203, sizeof(void*)*17, x_204);
x_205 = l_Array_empty(lean_box(0));
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_133);
x_207 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
lean_ctor_set(x_207, 2, x_176);
lean_ctor_set(x_207, 3, x_147);
x_208 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_208, 0, x_184);
lean_ctor_set(x_208, 1, x_203);
lean_ctor_set(x_208, 2, x_207);
lean_inc(x_148);
lean_inc(x_11);
x_209 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_209, 0, x_11);
lean_ctor_set(x_209, 1, x_136);
lean_ctor_set(x_209, 2, x_137);
lean_ctor_set(x_209, 3, x_148);
lean_ctor_set(x_209, 4, x_149);
lean_ctor_set(x_209, 5, x_150);
lean_ctor_set(x_209, 6, x_151);
lean_ctor_set(x_209, 7, x_152);
lean_ctor_set(x_209, 8, x_147);
lean_ctor_set(x_209, 9, x_154);
lean_ctor_set(x_209, 10, x_148);
lean_ctor_set(x_209, 11, x_155);
lean_ctor_set(x_209, 12, x_160);
lean_ctor_set(x_209, 13, x_175);
lean_ctor_set(x_209, 14, x_208);
lean_ctor_set(x_209, 15, x_129);
x_210 = lean_unbox(x_153);
lean_ctor_set_uint8(x_209, sizeof(void*)*16, x_210);
x_211 = lean_box(1);
x_212 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lam__0___boxed), 18, 10);
lean_closure_set(x_212, 0, x_209);
lean_closure_set(x_212, 1, x_24);
lean_closure_set(x_212, 2, x_211);
lean_closure_set(x_212, 3, x_153);
lean_closure_set(x_212, 4, x_147);
lean_closure_set(x_212, 5, x_21);
lean_closure_set(x_212, 6, x_27);
lean_closure_set(x_212, 7, x_31);
lean_closure_set(x_212, 8, x_126);
lean_closure_set(x_212, 9, x_2);
x_213 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_toGrindTactic_spec__0___redArg(x_11, x_212, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_130);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_126);
lean_free_object(x_29);
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
x_214 = lean_ctor_get(x_128, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_128, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_216 = x_128;
} else {
 lean_dec_ref(x_128);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_218 = lean_ctor_get(x_29, 0);
x_219 = lean_ctor_get(x_29, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_29);
x_220 = l_Lean_Meta_Grind_getNatZeroExpr___redArg(x_14, x_219);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_223 = x_220;
} else {
 lean_dec_ref(x_220);
 x_223 = lean_box(0);
}
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_11);
x_224 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkCleanState(x_11, x_2, x_15, x_16, x_17, x_18, x_222);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; size_t x_236; lean_object* x_237; lean_object* x_238; size_t x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = lean_ctor_get(x_2, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_2, 2);
lean_inc(x_228);
x_229 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_229);
x_230 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_230, 0, x_229);
lean_inc(x_229);
x_231 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_231, 0, x_229);
lean_inc(x_231);
x_232 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
lean_ctor_set(x_232, 2, x_231);
lean_inc(x_229);
x_233 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_233, 0, x_229);
x_234 = lean_unsigned_to_nat(2u);
x_235 = lean_unsigned_to_nat(5u);
x_236 = lean_usize_of_nat(x_235);
x_237 = lean_usize_to_nat(x_236);
x_238 = lean_nat_pow(x_234, x_237);
lean_dec(x_237);
x_239 = lean_usize_of_nat(x_238);
lean_dec(x_238);
x_240 = lean_usize_to_nat(x_239);
x_241 = lean_mk_empty_array_with_capacity(x_240);
lean_dec(x_240);
lean_inc(x_241);
x_242 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_242, 0, x_241);
x_243 = lean_unsigned_to_nat(0u);
lean_inc(x_241);
x_244 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_241);
lean_ctor_set(x_244, 2, x_243);
lean_ctor_set(x_244, 3, x_243);
lean_ctor_set_usize(x_244, 4, x_236);
lean_inc(x_229);
x_245 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_245, 0, x_229);
x_246 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__0(lean_box(0));
lean_inc(x_229);
x_247 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_247, 0, x_229);
x_248 = lean_mk_empty_array_with_capacity(x_243);
x_249 = lean_box(0);
x_250 = l_Std_Queue_empty(lean_box(0));
lean_inc(x_229);
x_251 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_251, 0, x_229);
lean_inc(x_241);
x_252 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_252, 0, x_241);
lean_inc(x_241);
x_253 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_241);
lean_ctor_set(x_253, 2, x_243);
lean_ctor_set(x_253, 3, x_243);
lean_ctor_set_usize(x_253, 4, x_236);
x_254 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__1(lean_box(0));
x_255 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Match_initFn____x40_Lean_Meta_Match_MatchEqsExt___hyg_181__spec__0(lean_box(0));
lean_inc(x_253);
x_256 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_256, 0, x_227);
lean_ctor_set(x_256, 1, x_243);
lean_ctor_set(x_256, 2, x_253);
lean_ctor_set(x_256, 3, x_253);
lean_ctor_set(x_256, 4, x_243);
lean_ctor_set(x_256, 5, x_243);
lean_ctor_set(x_256, 6, x_254);
lean_ctor_set(x_256, 7, x_243);
lean_ctor_set(x_256, 8, x_255);
x_257 = lean_box(0);
x_258 = lean_unsigned_to_nat(8u);
x_259 = lean_nat_shiftl(x_258, x_234);
x_260 = lean_unsigned_to_nat(3u);
x_261 = lean_nat_div(x_259, x_260);
lean_dec(x_259);
x_262 = l_Nat_nextPowerOfTwo(x_261);
lean_dec(x_261);
x_263 = lean_box(0);
lean_inc(x_262);
x_264 = lean_mk_array(x_262, x_263);
if (lean_is_scalar(x_223)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_223;
}
lean_ctor_set(x_265, 0, x_243);
lean_ctor_set(x_265, 1, x_264);
x_266 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__2(lean_box(0));
x_267 = lean_box(0);
x_268 = lean_box(0);
x_269 = lean_mk_array(x_262, x_268);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_243);
lean_ctor_set(x_270, 1, x_269);
lean_inc(x_229);
x_271 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_271, 0, x_229);
x_272 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_272, 0, x_243);
lean_ctor_set(x_272, 1, x_228);
lean_ctor_set(x_272, 2, x_257);
lean_ctor_set(x_272, 3, x_265);
lean_ctor_set(x_272, 4, x_266);
lean_ctor_set(x_272, 5, x_267);
lean_ctor_set(x_272, 6, x_257);
lean_ctor_set(x_272, 7, x_270);
lean_ctor_set(x_272, 8, x_271);
lean_inc(x_229);
x_273 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_273, 0, x_229);
lean_inc(x_229);
x_274 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_274, 0, x_229);
lean_inc(x_229);
x_275 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_275, 0, x_229);
lean_inc(x_241);
x_276 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_276, 0, x_241);
lean_inc(x_241);
x_277 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_241);
lean_ctor_set(x_277, 2, x_243);
lean_ctor_set(x_277, 3, x_243);
lean_ctor_set_usize(x_277, 4, x_236);
lean_inc(x_241);
x_278 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_278, 0, x_241);
lean_inc(x_241);
x_279 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_241);
lean_ctor_set(x_279, 2, x_243);
lean_ctor_set(x_279, 3, x_243);
lean_ctor_set_usize(x_279, 4, x_236);
x_280 = lean_box(0);
lean_inc(x_277);
lean_inc(x_273);
lean_inc(x_244);
x_281 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_281, 0, x_244);
lean_ctor_set(x_281, 1, x_273);
lean_ctor_set(x_281, 2, x_274);
lean_ctor_set(x_281, 3, x_275);
lean_ctor_set(x_281, 4, x_277);
lean_ctor_set(x_281, 5, x_277);
lean_ctor_set(x_281, 6, x_279);
lean_ctor_set(x_281, 7, x_280);
lean_inc(x_229);
x_282 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_282, 0, x_229);
lean_inc(x_229);
x_283 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_283, 0, x_229);
lean_inc(x_241);
x_284 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_284, 0, x_241);
lean_inc(x_241);
x_285 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_241);
lean_ctor_set(x_285, 2, x_243);
lean_ctor_set(x_285, 3, x_243);
lean_ctor_set_usize(x_285, 4, x_236);
lean_inc(x_241);
x_286 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_286, 0, x_241);
lean_inc(x_241);
x_287 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_241);
lean_ctor_set(x_287, 2, x_243);
lean_ctor_set(x_287, 3, x_243);
lean_ctor_set_usize(x_287, 4, x_236);
lean_inc(x_241);
x_288 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_288, 0, x_241);
lean_inc(x_241);
x_289 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_241);
lean_ctor_set(x_289, 2, x_243);
lean_ctor_set(x_289, 3, x_243);
lean_ctor_set_usize(x_289, 4, x_236);
lean_inc(x_241);
x_290 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_290, 0, x_241);
lean_inc(x_241);
x_291 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_241);
lean_ctor_set(x_291, 2, x_243);
lean_ctor_set(x_291, 3, x_243);
lean_ctor_set_usize(x_291, 4, x_236);
x_292 = lean_box(0);
lean_inc(x_241);
x_293 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_293, 0, x_241);
lean_inc(x_241);
x_294 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_241);
lean_ctor_set(x_294, 2, x_243);
lean_ctor_set(x_294, 3, x_243);
lean_ctor_set_usize(x_294, 4, x_236);
lean_inc(x_241);
x_295 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_295, 0, x_241);
x_296 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_241);
lean_ctor_set(x_296, 2, x_243);
lean_ctor_set(x_296, 3, x_243);
lean_ctor_set_usize(x_296, 4, x_236);
x_297 = lean_box(0);
lean_inc(x_229);
x_298 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_298, 0, x_229);
x_299 = l_Lean_PersistentHashMap_empty___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__3(lean_box(0));
lean_inc(x_287);
lean_inc_n(x_273, 2);
lean_inc(x_244);
x_300 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_300, 0, x_244);
lean_ctor_set(x_300, 1, x_273);
lean_ctor_set(x_300, 2, x_282);
lean_ctor_set(x_300, 3, x_283);
lean_ctor_set(x_300, 4, x_273);
lean_ctor_set(x_300, 5, x_285);
lean_ctor_set(x_300, 6, x_287);
lean_ctor_set(x_300, 7, x_287);
lean_ctor_set(x_300, 8, x_289);
lean_ctor_set(x_300, 9, x_291);
lean_ctor_set(x_300, 10, x_292);
lean_ctor_set(x_300, 11, x_294);
lean_ctor_set(x_300, 12, x_296);
lean_ctor_set(x_300, 13, x_243);
lean_ctor_set(x_300, 14, x_297);
lean_ctor_set(x_300, 15, x_298);
lean_ctor_set(x_300, 16, x_299);
x_301 = lean_unbox(x_249);
lean_ctor_set_uint8(x_300, sizeof(void*)*17, x_301);
x_302 = l_Array_empty(lean_box(0));
x_303 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_303, 0, x_229);
x_304 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
lean_ctor_set(x_304, 2, x_273);
lean_ctor_set(x_304, 3, x_243);
x_305 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_305, 0, x_281);
lean_ctor_set(x_305, 1, x_300);
lean_ctor_set(x_305, 2, x_304);
lean_inc(x_244);
lean_inc(x_11);
x_306 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_306, 0, x_11);
lean_ctor_set(x_306, 1, x_232);
lean_ctor_set(x_306, 2, x_233);
lean_ctor_set(x_306, 3, x_244);
lean_ctor_set(x_306, 4, x_245);
lean_ctor_set(x_306, 5, x_246);
lean_ctor_set(x_306, 6, x_247);
lean_ctor_set(x_306, 7, x_248);
lean_ctor_set(x_306, 8, x_243);
lean_ctor_set(x_306, 9, x_250);
lean_ctor_set(x_306, 10, x_244);
lean_ctor_set(x_306, 11, x_251);
lean_ctor_set(x_306, 12, x_256);
lean_ctor_set(x_306, 13, x_272);
lean_ctor_set(x_306, 14, x_305);
lean_ctor_set(x_306, 15, x_225);
x_307 = lean_unbox(x_249);
lean_ctor_set_uint8(x_306, sizeof(void*)*16, x_307);
x_308 = lean_box(1);
x_309 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lam__0___boxed), 18, 10);
lean_closure_set(x_309, 0, x_306);
lean_closure_set(x_309, 1, x_24);
lean_closure_set(x_309, 2, x_308);
lean_closure_set(x_309, 3, x_249);
lean_closure_set(x_309, 4, x_243);
lean_closure_set(x_309, 5, x_21);
lean_closure_set(x_309, 6, x_27);
lean_closure_set(x_309, 7, x_218);
lean_closure_set(x_309, 8, x_221);
lean_closure_set(x_309, 9, x_2);
x_310 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_toGrindTactic_spec__0___redArg(x_11, x_309, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_226);
return x_310;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_223);
lean_dec(x_221);
lean_dec(x_218);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
x_311 = lean_ctor_get(x_224, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_224, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_313 = x_224;
} else {
 lean_dec_ref(x_224);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_312);
return x_314;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__4(x_1, x_2, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__5_spec__5(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4_spec__5(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__8_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__8_spec__8(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal_spec__4_spec__8(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lam__0___boxed(lean_object** _args) {
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
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_3);
lean_dec(x_3);
x_20 = lean_unbox(x_4);
lean_dec(x_4);
x_21 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___lam__0(x_1, x_2, x_19, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_box(1);
x_15 = lean_unbox(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_Meta_Grind_Goal_checkInvariants(x_12, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_1 = x_13;
x_9 = x_17;
goto _start;
}
else
{
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore_spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*16);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
lean_ctor_set(x_1, 1, x_2);
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
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_2);
x_1 = x_10;
x_2 = x_11;
goto _start;
}
}
else
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_1 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_MVarId_ensureNoMVar(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Lean_MVarId_clearAuxDecls(x_1, x_6, x_7, x_8, x_9, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l_Lean_MVarId_revertAll(x_14, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_19 = l_Lean_MVarId_unfoldReducible(x_17, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_MVarId_betaReduce(x_20, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_mk_string_unchecked("grind", 5, 5);
x_26 = l_Lean_Name_mkStr1(x_25);
lean_inc(x_23);
x_27 = l_Lean_Meta_appendTagSuffix(x_23, x_26, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_29 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGoal(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_33 = l_Lean_Meta_Grind_intros(x_32, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_34);
x_36 = l_List_forM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore_spec__0(x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = lean_box(0);
x_40 = l_List_filterTR_loop___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore_spec__1(x_34, x_39);
lean_ctor_set(x_36, 0, x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_box(0);
x_43 = l_List_filterTR_loop___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore_spec__1(x_34, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_34);
x_45 = !lean_is_exclusive(x_36);
if (x_45 == 0)
{
return x_36;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_36, 0);
x_47 = lean_ctor_get(x_36, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_36);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_33;
}
}
else
{
uint8_t x_49; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_29);
if (x_49 == 0)
{
return x_29;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_29, 0);
x_51 = lean_ctor_get(x_29, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_29);
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
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
uint8_t x_57; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_22);
if (x_57 == 0)
{
return x_22;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_22, 0);
x_59 = lean_ctor_get(x_22, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_22);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_19);
if (x_61 == 0)
{
return x_19;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_19, 0);
x_63 = lean_ctor_get(x_19, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_19);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_16);
if (x_65 == 0)
{
return x_16;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_16, 0);
x_67 = lean_ctor_get(x_16, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_16);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_13);
if (x_69 == 0)
{
return x_13;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_13, 0);
x_71 = lean_ctor_get(x_13, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_13);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_11);
if (x_73 == 0)
{
return x_11;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_11, 0);
x_75 = lean_ctor_get(x_11, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_11);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1(x_14, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; double x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_uset(x_4, x_3, x_19);
x_22 = lean_float_of_nat(x_20);
x_23 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_23);
lean_inc(x_1);
x_24 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set_float(x_24, sizeof(void*)*2, x_22);
lean_ctor_set_float(x_24, sizeof(void*)*2 + 8, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 16, x_10);
x_25 = l_Lean_stringToMessageData(x_23);
lean_dec(x_23);
x_26 = l_Lean_MessageData_ofConst(x_17);
lean_inc(x_25);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_26);
lean_ctor_set(x_12, 0, x_25);
x_27 = lean_mk_string_unchecked(" ↦ ", 5, 3);
x_28 = l_Lean_stringToMessageData(x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___private_Init_Data_Repr_0__Nat_reprFast(x_15);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_MessageData_ofFormat(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
x_35 = lean_mk_empty_array_with_capacity(x_20);
x_36 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_usize_of_nat(x_37);
x_39 = lean_usize_add(x_3, x_38);
x_40 = lean_array_uset(x_21, x_3, x_36);
x_3 = x_39;
x_4 = x_40;
x_9 = x_18;
goto _start;
}
else
{
uint8_t x_42; 
lean_free_object(x_12);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_16);
if (x_42 == 0)
{
return x_16;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_16, 0);
x_44 = lean_ctor_get(x_16, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_16);
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
x_46 = lean_ctor_get(x_12, 0);
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_12);
x_48 = l_Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1(x_46, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; double x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; lean_object* x_73; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_box(0);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_array_uset(x_4, x_3, x_51);
x_54 = lean_float_of_nat(x_52);
x_55 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_55);
lean_inc(x_1);
x_56 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set_float(x_56, sizeof(void*)*2, x_54);
lean_ctor_set_float(x_56, sizeof(void*)*2 + 8, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*2 + 16, x_10);
x_57 = l_Lean_stringToMessageData(x_55);
lean_dec(x_55);
x_58 = l_Lean_MessageData_ofConst(x_49);
lean_inc(x_57);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_mk_string_unchecked(" ↦ ", 5, 3);
x_61 = l_Lean_stringToMessageData(x_60);
lean_dec(x_60);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
x_63 = l___private_Init_Data_Repr_0__Nat_reprFast(x_47);
x_64 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = l_Lean_MessageData_ofFormat(x_64);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_57);
x_68 = lean_mk_empty_array_with_capacity(x_52);
x_69 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_69, 0, x_56);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set(x_69, 2, x_68);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_usize_of_nat(x_70);
x_72 = lean_usize_add(x_3, x_71);
x_73 = lean_array_uset(x_53, x_3, x_69);
x_3 = x_72;
x_4 = x_73;
x_9 = x_50;
goto _start;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_47);
lean_dec(x_4);
lean_dec(x_1);
x_75 = lean_ctor_get(x_48, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_48, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_77 = x_48;
} else {
 lean_dec_ref(x_48);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_6, x_4);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = l_Lean_Name_lt(x_3, x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg___lam__0___boxed), 2, 0);
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
x_10 = l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg(x_8, x_2, x_7);
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
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg(x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_40; uint8_t x_41; 
x_9 = lean_unsigned_to_nat(0u);
x_40 = lean_array_get_size(x_3);
x_41 = lean_nat_dec_eq(x_40, x_9);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_47; 
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_40, x_42);
lean_dec(x_40);
x_47 = lean_nat_dec_le(x_9, x_43);
if (x_47 == 0)
{
lean_inc(x_43);
x_44 = x_43;
goto block_46;
}
else
{
x_44 = x_9;
goto block_46;
}
block_46:
{
lean_object* x_45; 
x_45 = l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg(x_3, x_44, x_43);
lean_dec(x_43);
x_10 = x_45;
goto block_39;
}
}
else
{
lean_dec(x_40);
x_10 = x_3;
goto block_39;
}
block_39:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_array_size(x_10);
x_12 = lean_usize_of_nat(x_9);
lean_inc(x_2);
x_13 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0(x_2, x_11, x_12, x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; double x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_float_of_nat(x_9);
x_17 = lean_box(1);
x_18 = lean_mk_string_unchecked("", 0, 0);
x_19 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_float(x_19, sizeof(void*)*2, x_16);
lean_ctor_set_float(x_19, sizeof(void*)*2 + 8, x_16);
x_20 = lean_unbox(x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 16, x_20);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = l_Lean_MessageData_ofFormat(x_21);
x_23 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_15);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; double x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_float_of_nat(x_9);
x_27 = lean_box(1);
x_28 = lean_mk_string_unchecked("", 0, 0);
x_29 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set_float(x_29, sizeof(void*)*2, x_26);
lean_ctor_set_float(x_29, sizeof(void*)*2 + 8, x_26);
x_30 = lean_unbox(x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*2 + 16, x_30);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_1);
x_32 = l_Lean_MessageData_ofFormat(x_31);
x_33 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_24);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
return x_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___redArg___lam__0), 3, 0);
x_3 = l_Lean_Meta_Grind_instBEqOrigin__1;
x_4 = l_Lean_Meta_Grind_instHashableOrigin;
x_5 = lean_box(0);
x_6 = l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl_spec__0(lean_box(0), x_3, x_4, lean_box(0), lean_box(0), x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_12, 0, x_16);
x_17 = lean_array_push(x_4, x_12);
x_5 = x_17;
goto block_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_array_push(x_4, x_20);
x_5 = x_21;
goto block_10;
}
}
else
{
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
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_nat_dec_lt(x_2, x_3);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_le(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
return x_5;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_2);
x_10 = lean_usize_of_nat(x_3);
x_11 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1_spec__1(x_1, x_9, x_10, x_5);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = l_Lean_Meta_Grind_isBuiltinEagerCases(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_array_push(x_4, x_12);
x_5 = x_15;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___redArg(x_8);
x_10 = lean_array_mk(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_79 = lean_array_get_size(x_10);
x_80 = l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1(x_10, x_11, x_79);
lean_dec(x_79);
lean_dec(x_10);
x_96 = lean_ctor_get(x_1, 1);
x_97 = l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__14___redArg(x_96);
x_98 = lean_array_mk(x_97);
x_99 = lean_array_get_size(x_98);
x_100 = lean_mk_empty_array_with_capacity(x_11);
x_101 = lean_nat_dec_lt(x_11, x_99);
if (x_101 == 0)
{
lean_dec(x_99);
lean_dec(x_98);
x_81 = x_100;
goto block_95;
}
else
{
uint8_t x_102; 
x_102 = lean_nat_dec_le(x_99, x_99);
if (x_102 == 0)
{
lean_dec(x_99);
lean_dec(x_98);
x_81 = x_100;
goto block_95;
}
else
{
size_t x_103; size_t x_104; lean_object* x_105; 
x_103 = lean_usize_of_nat(x_11);
x_104 = lean_usize_of_nat(x_99);
lean_dec(x_99);
x_105 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__3(x_98, x_103, x_104, x_100);
lean_dec(x_98);
x_81 = x_105;
goto block_95;
}
}
block_30:
{
uint8_t x_14; 
x_14 = l_Array_isEmpty___redArg(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; double x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_box(1);
x_16 = lean_mk_string_unchecked("grind", 5, 5);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_float_of_nat(x_11);
x_19 = lean_mk_string_unchecked("", 0, 0);
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_18);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_18);
x_21 = lean_unbox(x_15);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_21);
x_22 = lean_mk_string_unchecked("Diagnostics", 11, 11);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_MessageData_ofFormat(x_23);
x_25 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_12);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_13);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_13);
return x_29;
}
}
block_58:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
lean_dec(x_2);
x_38 = l_Lean_Meta_Simp_mkDiagMessages(x_37, x_32, x_33, x_34, x_35, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Array_isEmpty___redArg(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; double x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_42 = lean_box(1);
x_43 = lean_mk_string_unchecked("grind", 5, 5);
x_44 = l_Lean_Name_mkStr1(x_43);
x_45 = lean_float_of_nat(x_11);
x_46 = lean_mk_string_unchecked("", 0, 0);
x_47 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_float(x_47, sizeof(void*)*2, x_45);
lean_ctor_set_float(x_47, sizeof(void*)*2 + 8, x_45);
x_48 = lean_unbox(x_42);
lean_ctor_set_uint8(x_47, sizeof(void*)*2 + 16, x_48);
x_49 = lean_mk_string_unchecked("Simplifier", 10, 10);
x_50 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Lean_MessageData_ofFormat(x_50);
x_52 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_39);
x_53 = lean_array_push(x_31, x_52);
x_12 = x_53;
x_13 = x_40;
goto block_30;
}
else
{
lean_dec(x_39);
x_12 = x_31;
x_13 = x_40;
goto block_30;
}
}
else
{
uint8_t x_54; 
lean_dec(x_31);
x_54 = !lean_is_exclusive(x_38);
if (x_54 == 0)
{
return x_38;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_38, 0);
x_56 = lean_ctor_get(x_38, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_38);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
block_78:
{
uint8_t x_66; 
x_66 = l_Array_isEmpty___redArg(x_59);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_mk_string_unchecked("Cases instances", 15, 15);
x_68 = lean_mk_string_unchecked("cases", 5, 5);
x_69 = l_Lean_Name_mkStr1(x_68);
x_70 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData(x_67, x_69, x_59, x_61, x_62, x_63, x_64, x_65);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_array_push(x_60, x_71);
x_31 = x_73;
x_32 = x_61;
x_33 = x_62;
x_34 = x_63;
x_35 = x_64;
x_36 = x_72;
goto block_58;
}
else
{
uint8_t x_74; 
lean_dec(x_60);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_70);
if (x_74 == 0)
{
return x_70;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_70, 0);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_70);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_dec(x_59);
x_31 = x_60;
x_32 = x_61;
x_33 = x_62;
x_34 = x_63;
x_35 = x_64;
x_36 = x_65;
goto block_58;
}
}
block_95:
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_mk_empty_array_with_capacity(x_11);
x_83 = l_Array_isEmpty___redArg(x_80);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_mk_string_unchecked("E-Matching instances", 20, 20);
x_85 = lean_mk_string_unchecked("thm", 3, 3);
x_86 = l_Lean_Name_mkStr1(x_85);
x_87 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_countersToMessageData(x_84, x_86, x_80, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_array_push(x_82, x_88);
x_59 = x_81;
x_60 = x_90;
x_61 = x_3;
x_62 = x_4;
x_63 = x_5;
x_64 = x_6;
x_65 = x_89;
goto block_78;
}
else
{
uint8_t x_91; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_87);
if (x_91 == 0)
{
return x_87;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_87, 0);
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_87);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_dec(x_80);
x_59 = x_81;
x_60 = x_82;
x_61 = x_3;
x_62 = x_4;
x_63 = x_5;
x_64 = x_6;
x_65 = x_7;
goto block_78;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_toList___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag_spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Result_hasFailures(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_List_isEmpty___redArg(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_hasFailures___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Result_hasFailures(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Grind_Result_toMessageData_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_9 = l_List_reverse___redArg(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Meta_Grind_goalToMessageData(x_12, x_14, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_16);
{
lean_object* _tmp_1 = x_13;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_7 = x_17;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_8 = _tmp_7;
}
goto _start;
}
else
{
uint8_t x_19; 
lean_free_object(x_2);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 3);
lean_inc(x_25);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_26 = l_Lean_Meta_Grind_goalToMessageData(x_23, x_25, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_3);
x_2 = x_24;
x_3 = x_29;
x_8 = x_28;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_33 = x_26;
} else {
 lean_dec_ref(x_26);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_mk_string_unchecked("\n", 1, 1);
x_9 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
x_10 = l_Lean_MessageData_joinSep(x_1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_9 = l_List_mapM_loop___at___Lean_Meta_Grind_Result_toMessageData_spec__0(x_1, x_7, x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_36; uint8_t x_37; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_36 = lean_ctor_get(x_1, 3);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_36, sizeof(void*)*7 + 10);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_1);
x_38 = lean_box(0);
x_39 = l_Lean_Meta_Grind_Result_toMessageData___lam__0(x_10, x_38, x_2, x_3, x_4, x_5, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_39;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_1, 2);
lean_inc(x_40);
x_41 = l_List_isEmpty___redArg(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; double x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_42 = lean_mk_string_unchecked("grind", 5, 5);
x_43 = l_Lean_Name_mkStr1(x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_float_of_nat(x_44);
x_46 = lean_mk_string_unchecked("", 0, 0);
x_47 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_float(x_47, sizeof(void*)*2, x_45);
lean_ctor_set_float(x_47, sizeof(void*)*2 + 8, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*2 + 16, x_37);
x_48 = lean_mk_string_unchecked("Issues", 6, 6);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_MessageData_ofFormat(x_49);
x_51 = l_List_reverse___redArg(x_40);
x_52 = lean_array_mk(x_51);
x_53 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_50);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_8);
x_55 = l_List_appendTR(lean_box(0), x_10, x_54);
x_12 = x_55;
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_11;
goto block_35;
}
else
{
lean_dec(x_40);
x_12 = x_10;
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_11;
goto block_35;
}
}
block_35:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_1, 5);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 6);
lean_inc(x_19);
lean_dec(x_1);
x_20 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag(x_18, x_19, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = l_Lean_Meta_Grind_Result_toMessageData___lam__0(x_12, x_23, x_13, x_14, x_15, x_16, x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_8);
x_28 = l_List_appendTR(lean_box(0), x_12, x_27);
x_29 = lean_box(0);
x_30 = l_Lean_Meta_Grind_Result_toMessageData___lam__0(x_28, x_29, x_13, x_14, x_15, x_16, x_25);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_9);
if (x_56 == 0)
{
return x_9;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_9, 0);
x_58 = lean_ctor_get(x_9, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_9);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Grind_Result_toMessageData_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_mapM_loop___at___Lean_Meta_Grind_Result_toMessageData_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_Result_toMessageData___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Result_toMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_Result_toMessageData(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_18; uint8_t x_19; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_18 = lean_mk_string_unchecked("trace", 5, 5);
x_19 = lean_string_dec_eq(x_5, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
x_6 = x_1;
goto block_17;
}
else
{
x_6 = x_2;
goto block_17;
}
block_17:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_mk_string_unchecked("Elab", 4, 4);
x_10 = lean_string_dec_eq(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_mk_string_unchecked("Tactic", 6, 6);
x_12 = lean_string_dec_eq(x_8, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
if (lean_obj_tag(x_7) == 0)
{
return x_1;
}
else
{
return x_1;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_mk_string_unchecked("unsolvedGoals", 13, 13);
x_14 = lean_string_dec_eq(x_5, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
if (lean_obj_tag(x_7) == 0)
{
return x_1;
}
else
{
return x_1;
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
return x_2;
}
else
{
return x_1;
}
}
}
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_mk_string_unchecked("synthPlaceholder", 16, 16);
x_16 = lean_string_dec_eq(x_5, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
if (lean_obj_tag(x_7) == 0)
{
return x_1;
}
else
{
return x_1;
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
return x_2;
}
else
{
return x_1;
}
}
}
}
default: 
{
return x_1;
}
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; uint8_t x_103; uint8_t x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; uint8_t x_111; uint8_t x_112; uint8_t x_113; lean_object* x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_127; uint8_t x_137; uint8_t x_138; 
x_120 = lean_box(2);
x_137 = lean_unbox(x_120);
x_138 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_107_(x_3, x_137);
if (x_138 == 0)
{
x_127 = x_138;
goto block_136;
}
else
{
uint8_t x_139; 
lean_inc(x_2);
x_139 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_127 = x_139;
goto block_136;
}
block_65:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_17, 6);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 7);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_st_ref_take(x_18, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 0, x_20);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_12);
x_27 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_15);
lean_ctor_set(x_27, 2, x_16);
lean_ctor_set(x_27, 3, x_14);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_11);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 1, x_10);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 2, x_4);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_24, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_24, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_24, 5);
lean_inc(x_33);
x_34 = l_Lean_MessageLog_add(x_27, x_33);
x_35 = lean_ctor_get(x_24, 6);
lean_inc(x_35);
x_36 = lean_ctor_get(x_24, 7);
lean_inc(x_36);
lean_dec(x_24);
x_37 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 3, x_31);
lean_ctor_set(x_37, 4, x_32);
lean_ctor_set(x_37, 5, x_34);
lean_ctor_set(x_37, 6, x_35);
lean_ctor_set(x_37, 7, x_36);
x_38 = lean_st_ref_set(x_18, x_37, x_25);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_45 = lean_ctor_get(x_22, 0);
x_46 = lean_ctor_get(x_22, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_22);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_20);
lean_ctor_set(x_47, 1, x_21);
x_48 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_12);
x_49 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_49, 0, x_13);
lean_ctor_set(x_49, 1, x_15);
lean_ctor_set(x_49, 2, x_16);
lean_ctor_set(x_49, 3, x_14);
lean_ctor_set(x_49, 4, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*5, x_11);
lean_ctor_set_uint8(x_49, sizeof(void*)*5 + 1, x_10);
lean_ctor_set_uint8(x_49, sizeof(void*)*5 + 2, x_4);
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_45, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_45, 3);
lean_inc(x_53);
x_54 = lean_ctor_get(x_45, 4);
lean_inc(x_54);
x_55 = lean_ctor_get(x_45, 5);
lean_inc(x_55);
x_56 = l_Lean_MessageLog_add(x_49, x_55);
x_57 = lean_ctor_get(x_45, 6);
lean_inc(x_57);
x_58 = lean_ctor_get(x_45, 7);
lean_inc(x_58);
lean_dec(x_45);
x_59 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_51);
lean_ctor_set(x_59, 2, x_52);
lean_ctor_set(x_59, 3, x_53);
lean_ctor_set(x_59, 4, x_54);
lean_ctor_set(x_59, 5, x_56);
lean_ctor_set(x_59, 6, x_57);
lean_ctor_set(x_59, 7, x_58);
x_60 = lean_st_ref_set(x_18, x_59, x_46);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
block_102:
{
lean_object* x_71; uint8_t x_72; 
x_71 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_2, x_5, x_6, x_7, x_8, x_9);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
x_75 = lean_ctor_get(x_7, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_7, 0);
lean_inc(x_76);
lean_inc(x_75);
x_77 = l_Lean_FileMap_toPosition(x_75, x_69);
lean_dec(x_69);
x_78 = l_Lean_FileMap_toPosition(x_75, x_70);
lean_dec(x_70);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_mk_string_unchecked("", 0, 0);
x_81 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
if (x_81 == 0)
{
lean_free_object(x_71);
x_10 = x_68;
x_11 = x_67;
x_12 = x_73;
x_13 = x_76;
x_14 = x_80;
x_15 = x_77;
x_16 = x_79;
x_17 = x_7;
x_18 = x_8;
x_19 = x_74;
goto block_65;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_box(x_66);
x_83 = lean_box(x_81);
x_84 = lean_alloc_closure((void*)(l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_84, 0, x_82);
lean_closure_set(x_84, 1, x_83);
lean_inc(x_73);
x_85 = l_Lean_MessageData_hasTag(x_84, x_73);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_73);
lean_dec(x_7);
x_86 = lean_box(0);
lean_ctor_set(x_71, 0, x_86);
return x_71;
}
else
{
lean_free_object(x_71);
x_10 = x_68;
x_11 = x_67;
x_12 = x_73;
x_13 = x_76;
x_14 = x_80;
x_15 = x_77;
x_16 = x_79;
x_17 = x_7;
x_18 = x_8;
x_19 = x_74;
goto block_65;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_87 = lean_ctor_get(x_71, 0);
x_88 = lean_ctor_get(x_71, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_71);
x_89 = lean_ctor_get(x_7, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_7, 0);
lean_inc(x_90);
lean_inc(x_89);
x_91 = l_Lean_FileMap_toPosition(x_89, x_69);
lean_dec(x_69);
x_92 = l_Lean_FileMap_toPosition(x_89, x_70);
lean_dec(x_70);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_mk_string_unchecked("", 0, 0);
x_95 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
if (x_95 == 0)
{
x_10 = x_68;
x_11 = x_67;
x_12 = x_87;
x_13 = x_90;
x_14 = x_94;
x_15 = x_91;
x_16 = x_93;
x_17 = x_7;
x_18 = x_8;
x_19 = x_88;
goto block_65;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_96 = lean_box(x_66);
x_97 = lean_box(x_95);
x_98 = lean_alloc_closure((void*)(l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_98, 0, x_96);
lean_closure_set(x_98, 1, x_97);
lean_inc(x_87);
x_99 = l_Lean_MessageData_hasTag(x_98, x_87);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_7);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_88);
return x_101;
}
else
{
x_10 = x_68;
x_11 = x_67;
x_12 = x_87;
x_13 = x_90;
x_14 = x_94;
x_15 = x_91;
x_16 = x_93;
x_17 = x_7;
x_18 = x_8;
x_19 = x_88;
goto block_65;
}
}
}
}
block_110:
{
lean_object* x_108; 
x_108 = l_Lean_Syntax_getTailPos_x3f(x_106, x_105);
lean_dec(x_106);
if (lean_obj_tag(x_108) == 0)
{
lean_inc(x_107);
x_66 = x_103;
x_67 = x_105;
x_68 = x_104;
x_69 = x_107;
x_70 = x_107;
goto block_102;
}
else
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec(x_108);
x_66 = x_103;
x_67 = x_105;
x_68 = x_104;
x_69 = x_107;
x_70 = x_109;
goto block_102;
}
}
block_119:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_7, 5);
lean_inc(x_114);
x_115 = l_Lean_replaceRef(x_1, x_114);
lean_dec(x_114);
x_116 = l_Lean_Syntax_getPos_x3f(x_115, x_112);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; 
x_117 = lean_unsigned_to_nat(0u);
x_103 = x_111;
x_104 = x_113;
x_105 = x_112;
x_106 = x_115;
x_107 = x_117;
goto block_110;
}
else
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
lean_dec(x_116);
x_103 = x_111;
x_104 = x_113;
x_105 = x_112;
x_106 = x_115;
x_107 = x_118;
goto block_110;
}
}
block_126:
{
if (x_123 == 0)
{
if (x_122 == 0)
{
x_111 = x_121;
x_112 = x_122;
x_113 = x_3;
goto block_119;
}
else
{
uint8_t x_124; 
x_124 = lean_unbox(x_120);
x_111 = x_121;
x_112 = x_122;
x_113 = x_124;
goto block_119;
}
}
else
{
uint8_t x_125; 
x_125 = lean_unbox(x_120);
x_111 = x_121;
x_112 = x_122;
x_113 = x_125;
goto block_119;
}
}
block_136:
{
if (x_127 == 0)
{
lean_object* x_128; uint8_t x_129; uint8_t x_130; 
x_128 = lean_box(1);
x_129 = lean_unbox(x_128);
x_130 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_107_(x_3, x_129);
if (x_130 == 0)
{
x_121 = x_127;
x_122 = x_127;
x_123 = x_130;
goto block_126;
}
else
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_131 = lean_ctor_get(x_7, 2);
lean_inc(x_131);
x_132 = l_Lean_warningAsError;
x_133 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_131, x_132);
lean_dec(x_131);
x_121 = x_127;
x_122 = x_127;
x_123 = x_133;
goto block_126;
}
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_7);
lean_dec(x_2);
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_9);
return x_135;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_8, 5);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg(x_11, x_1, x_2, x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___Lean_Meta_Grind_main_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; uint64_t x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_14 = lean_ctor_get(x_9, 0);
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
lean_ctor_set_uint8(x_32, 9, x_1);
lean_ctor_set_uint8(x_32, 10, x_24);
lean_ctor_set_uint8(x_32, 11, x_25);
lean_ctor_set_uint8(x_32, 12, x_26);
lean_ctor_set_uint8(x_32, 13, x_27);
lean_ctor_set_uint8(x_32, 14, x_28);
lean_ctor_set_uint8(x_32, 15, x_29);
lean_ctor_set_uint8(x_32, 16, x_30);
lean_ctor_set_uint8(x_32, 17, x_31);
x_33 = lean_ctor_get_uint64(x_9, sizeof(void*)*7);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_uint64_of_nat(x_34);
x_36 = lean_uint64_shift_right(x_33, x_35);
x_37 = lean_uint64_shift_left(x_36, x_35);
x_38 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_39 = lean_uint64_lor(x_37, x_38);
x_40 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 8);
x_41 = lean_ctor_get(x_9, 1);
x_42 = lean_ctor_get(x_9, 2);
x_43 = lean_ctor_get(x_9, 3);
x_44 = lean_ctor_get(x_9, 4);
x_45 = lean_ctor_get(x_9, 5);
x_46 = lean_ctor_get(x_9, 6);
x_47 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 9);
x_48 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 10);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
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
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_50 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_initCore(x_2, x_3, x_6, x_7, x_8, x_49, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_49);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_51);
x_53 = l_Lean_Meta_Grind_solve(x_51, x_4, x_6, x_7, x_8, x_49, x_10, x_11, x_12, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
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
x_57 = !lean_is_exclusive(x_54);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_58 = lean_ctor_get(x_54, 0);
x_59 = lean_ctor_get(x_54, 1);
x_111 = lean_mk_string_unchecked("debug", 5, 5);
x_112 = lean_mk_string_unchecked("final", 5, 5);
x_113 = l_Lean_Name_mkStr3(x_5, x_111, x_112);
lean_inc(x_113);
x_114 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_reportIssue_spec__0___redArg(x_113, x_11, x_55);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; 
lean_dec(x_113);
lean_free_object(x_54);
lean_dec(x_51);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_69 = x_6;
x_70 = x_7;
x_71 = x_8;
x_72 = x_49;
x_73 = x_10;
x_74 = x_11;
x_75 = x_12;
x_76 = x_117;
goto block_110;
}
else
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_114);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_114, 1);
x_120 = lean_ctor_get(x_114, 0);
lean_dec(x_120);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_49);
x_121 = l_Lean_Meta_Grind_ppGoals(x_51, x_49, x_10, x_11, x_12, x_119);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_mk_string_unchecked("", 0, 0);
x_125 = l_Lean_stringToMessageData(x_124);
lean_dec(x_124);
lean_inc(x_125);
lean_ctor_set_tag(x_114, 7);
lean_ctor_set(x_114, 1, x_122);
lean_ctor_set(x_114, 0, x_125);
lean_ctor_set_tag(x_54, 7);
lean_ctor_set(x_54, 1, x_125);
lean_ctor_set(x_54, 0, x_114);
x_126 = l_Lean_addTrace___at___Lean_Meta_Grind_reportIssue_spec__1___redArg(x_113, x_54, x_49, x_10, x_11, x_12, x_123);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec(x_126);
x_69 = x_6;
x_70 = x_7;
x_71 = x_8;
x_72 = x_49;
x_73 = x_10;
x_74 = x_11;
x_75 = x_12;
x_76 = x_127;
goto block_110;
}
else
{
uint8_t x_128; 
lean_free_object(x_114);
lean_dec(x_113);
lean_free_object(x_54);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_49);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_128 = !lean_is_exclusive(x_121);
if (x_128 == 0)
{
return x_121;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_121, 0);
x_130 = lean_ctor_get(x_121, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_121);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_114, 1);
lean_inc(x_132);
lean_dec(x_114);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_49);
x_133 = l_Lean_Meta_Grind_ppGoals(x_51, x_49, x_10, x_11, x_12, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_mk_string_unchecked("", 0, 0);
x_137 = l_Lean_stringToMessageData(x_136);
lean_dec(x_136);
lean_inc(x_137);
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_134);
lean_ctor_set_tag(x_54, 7);
lean_ctor_set(x_54, 1, x_137);
lean_ctor_set(x_54, 0, x_138);
x_139 = l_Lean_addTrace___at___Lean_Meta_Grind_reportIssue_spec__1___redArg(x_113, x_54, x_49, x_10, x_11, x_12, x_135);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_69 = x_6;
x_70 = x_7;
x_71 = x_8;
x_72 = x_49;
x_73 = x_10;
x_74 = x_11;
x_75 = x_12;
x_76 = x_140;
goto block_110;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_113);
lean_free_object(x_54);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_49);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_141 = lean_ctor_get(x_133, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_133, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_143 = x_133;
} else {
 lean_dec_ref(x_133);
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
}
block_68:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_3, 0);
lean_inc(x_65);
lean_dec(x_3);
x_66 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_59);
lean_ctor_set(x_66, 2, x_61);
lean_ctor_set(x_66, 3, x_65);
lean_ctor_set(x_66, 4, x_60);
lean_ctor_set(x_66, 5, x_63);
lean_ctor_set(x_66, 6, x_62);
if (lean_is_scalar(x_56)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_56;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
block_110:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_77 = lean_st_ref_get(x_71, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_st_ref_get(x_71, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_st_ref_get(x_71, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_st_ref_get(x_71, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_78, 10);
lean_inc(x_89);
lean_dec(x_78);
x_90 = lean_ctor_get(x_81, 11);
lean_inc(x_90);
lean_dec(x_81);
x_91 = lean_ctor_get(x_84, 12);
lean_inc(x_91);
lean_dec(x_84);
x_92 = lean_ctor_get(x_87, 3);
lean_inc(x_92);
lean_dec(x_87);
x_93 = l_List_isEmpty___redArg(x_58);
if (x_93 == 0)
{
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
x_60 = x_90;
x_61 = x_89;
x_62 = x_92;
x_63 = x_91;
x_64 = x_88;
goto block_68;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = l_Lean_isDiagnosticsEnabled___redArg(x_74, x_88);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_unbox(x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_60 = x_90;
x_61 = x_89;
x_62 = x_92;
x_63 = x_91;
x_64 = x_97;
goto block_68;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
lean_inc(x_92);
x_99 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag(x_91, x_92, x_72, x_73, x_74, x_75, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_60 = x_90;
x_61 = x_89;
x_62 = x_92;
x_63 = x_91;
x_64 = x_101;
goto block_68;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_ctor_get(x_100, 0);
lean_inc(x_103);
lean_dec(x_100);
x_104 = l_Lean_logInfo___at___Lean_Meta_Grind_main_spec__0(x_103, x_69, x_70, x_71, x_72, x_73, x_74, x_75, x_102);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_60 = x_90;
x_61 = x_89;
x_62 = x_92;
x_63 = x_91;
x_64 = x_105;
goto block_68;
}
}
else
{
uint8_t x_106; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_3);
x_106 = !lean_is_exclusive(x_99);
if (x_106 == 0)
{
return x_99;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_99, 0);
x_108 = lean_ctor_get(x_99, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_99);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_145 = lean_ctor_get(x_54, 0);
x_146 = lean_ctor_get(x_54, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_54);
x_198 = lean_mk_string_unchecked("debug", 5, 5);
x_199 = lean_mk_string_unchecked("final", 5, 5);
x_200 = l_Lean_Name_mkStr3(x_5, x_198, x_199);
lean_inc(x_200);
x_201 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_reportIssue_spec__0___redArg(x_200, x_11, x_55);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_unbox(x_202);
lean_dec(x_202);
if (x_203 == 0)
{
lean_object* x_204; 
lean_dec(x_200);
lean_dec(x_51);
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
lean_dec(x_201);
x_156 = x_6;
x_157 = x_7;
x_158 = x_8;
x_159 = x_49;
x_160 = x_10;
x_161 = x_11;
x_162 = x_12;
x_163 = x_204;
goto block_197;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_201, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_206 = x_201;
} else {
 lean_dec_ref(x_201);
 x_206 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_49);
x_207 = l_Lean_Meta_Grind_ppGoals(x_51, x_49, x_10, x_11, x_12, x_205);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = lean_mk_string_unchecked("", 0, 0);
x_211 = l_Lean_stringToMessageData(x_210);
lean_dec(x_210);
lean_inc(x_211);
if (lean_is_scalar(x_206)) {
 x_212 = lean_alloc_ctor(7, 2, 0);
} else {
 x_212 = x_206;
 lean_ctor_set_tag(x_212, 7);
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_208);
x_213 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
x_214 = l_Lean_addTrace___at___Lean_Meta_Grind_reportIssue_spec__1___redArg(x_200, x_213, x_49, x_10, x_11, x_12, x_209);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec(x_214);
x_156 = x_6;
x_157 = x_7;
x_158 = x_8;
x_159 = x_49;
x_160 = x_10;
x_161 = x_11;
x_162 = x_12;
x_163 = x_215;
goto block_197;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_206);
lean_dec(x_200);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_56);
lean_dec(x_49);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_216 = lean_ctor_get(x_207, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_207, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_218 = x_207;
} else {
 lean_dec_ref(x_207);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
block_155:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_3, 0);
lean_inc(x_152);
lean_dec(x_3);
x_153 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_153, 0, x_145);
lean_ctor_set(x_153, 1, x_146);
lean_ctor_set(x_153, 2, x_148);
lean_ctor_set(x_153, 3, x_152);
lean_ctor_set(x_153, 4, x_147);
lean_ctor_set(x_153, 5, x_150);
lean_ctor_set(x_153, 6, x_149);
if (lean_is_scalar(x_56)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_56;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_151);
return x_154;
}
block_197:
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_164 = lean_st_ref_get(x_158, x_163);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_st_ref_get(x_158, x_166);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_st_ref_get(x_158, x_169);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_st_ref_get(x_158, x_172);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_ctor_get(x_165, 10);
lean_inc(x_176);
lean_dec(x_165);
x_177 = lean_ctor_get(x_168, 11);
lean_inc(x_177);
lean_dec(x_168);
x_178 = lean_ctor_get(x_171, 12);
lean_inc(x_178);
lean_dec(x_171);
x_179 = lean_ctor_get(x_174, 3);
lean_inc(x_179);
lean_dec(x_174);
x_180 = l_List_isEmpty___redArg(x_145);
if (x_180 == 0)
{
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_147 = x_177;
x_148 = x_176;
x_149 = x_179;
x_150 = x_178;
x_151 = x_175;
goto block_155;
}
else
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_181 = l_Lean_isDiagnosticsEnabled___redArg(x_161, x_175);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_unbox(x_182);
lean_dec(x_182);
if (x_183 == 0)
{
lean_object* x_184; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_184 = lean_ctor_get(x_181, 1);
lean_inc(x_184);
lean_dec(x_181);
x_147 = x_177;
x_148 = x_176;
x_149 = x_179;
x_150 = x_178;
x_151 = x_184;
goto block_155;
}
else
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_181, 1);
lean_inc(x_185);
lean_dec(x_181);
lean_inc(x_179);
x_186 = l___private_Lean_Meta_Tactic_Grind_Main_0__Lean_Meta_Grind_mkGlobalDiag(x_178, x_179, x_159, x_160, x_161, x_162, x_185);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_147 = x_177;
x_148 = x_176;
x_149 = x_179;
x_150 = x_178;
x_151 = x_188;
goto block_155;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
lean_dec(x_186);
x_190 = lean_ctor_get(x_187, 0);
lean_inc(x_190);
lean_dec(x_187);
x_191 = l_Lean_logInfo___at___Lean_Meta_Grind_main_spec__0(x_190, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_189);
lean_dec(x_162);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_147 = x_177;
x_148 = x_176;
x_149 = x_179;
x_150 = x_178;
x_151 = x_192;
goto block_155;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_56);
lean_dec(x_3);
x_193 = lean_ctor_get(x_186, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_186, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_195 = x_186;
} else {
 lean_dec_ref(x_186);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
}
}
}
}
}
else
{
uint8_t x_220; 
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_220 = !lean_is_exclusive(x_53);
if (x_220 == 0)
{
return x_53;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_53, 0);
x_222 = lean_ctor_get(x_53, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_53);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
}
else
{
uint8_t x_224; 
lean_dec(x_49);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_224 = !lean_is_exclusive(x_50);
if (x_224 == 0)
{
return x_50;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_50, 0);
x_226 = lean_ctor_get(x_50, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_50);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = l_Lean_Meta_debug_terminalTacticsAsSorry;
x_13 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box(2);
lean_inc(x_3);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_main___lam__0___boxed), 13, 5);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_4);
x_16 = l_Lean_Meta_Grind_GrindM_run___redArg(x_15, x_5, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = l_Lean_MVarId_admit(x_1, x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; lean_object* x_36; lean_object* x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = lean_box(0);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec(x_2);
x_23 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0(lean_box(0));
x_24 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Match_initFn____x40_Lean_Meta_Match_MatchEqsExt___hyg_181__spec__0(lean_box(0));
lean_inc(x_24);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_24);
x_26 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_26);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_inc(x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_26);
lean_inc(x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_26);
x_31 = lean_unsigned_to_nat(0u);
lean_inc(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_unsigned_to_nat(5u);
x_35 = lean_usize_of_nat(x_34);
x_36 = lean_usize_to_nat(x_35);
x_37 = lean_nat_pow(x_33, x_36);
lean_dec(x_36);
x_38 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_39 = lean_usize_to_nat(x_38);
x_40 = lean_mk_empty_array_with_capacity(x_39);
lean_dec(x_39);
lean_inc(x_40);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_31);
lean_ctor_set(x_42, 3, x_31);
lean_ctor_set_usize(x_42, 4, x_35);
lean_inc(x_30);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_30);
lean_ctor_set(x_43, 1, x_30);
lean_ctor_set(x_43, 2, x_28);
lean_ctor_set(x_43, 3, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_32);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_45, 0, x_20);
lean_ctor_set(x_45, 1, x_20);
lean_ctor_set(x_45, 2, x_21);
lean_ctor_set(x_45, 3, x_22);
lean_ctor_set(x_45, 4, x_25);
lean_ctor_set(x_45, 5, x_29);
lean_ctor_set(x_45, 6, x_44);
lean_ctor_set(x_17, 0, x_45);
return x_17;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; lean_object* x_63; lean_object* x_64; size_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_46 = lean_ctor_get(x_17, 1);
lean_inc(x_46);
lean_dec(x_17);
x_47 = lean_box(0);
x_48 = lean_box(0);
x_49 = lean_ctor_get(x_2, 0);
lean_inc(x_49);
lean_dec(x_2);
x_50 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_GrindM_run_spec__0(lean_box(0));
x_51 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Match_initFn____x40_Lean_Meta_Match_MatchEqsExt___hyg_181__spec__0(lean_box(0));
lean_inc(x_51);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_51);
x_53 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_53);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_inc(x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_53);
lean_inc(x_55);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_53);
x_58 = lean_unsigned_to_nat(0u);
lean_inc(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_unsigned_to_nat(2u);
x_61 = lean_unsigned_to_nat(5u);
x_62 = lean_usize_of_nat(x_61);
x_63 = lean_usize_to_nat(x_62);
x_64 = lean_nat_pow(x_60, x_63);
lean_dec(x_63);
x_65 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_66 = lean_usize_to_nat(x_65);
x_67 = lean_mk_empty_array_with_capacity(x_66);
lean_dec(x_66);
lean_inc(x_67);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set(x_69, 2, x_58);
lean_ctor_set(x_69, 3, x_58);
lean_ctor_set_usize(x_69, 4, x_62);
lean_inc(x_57);
x_70 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_70, 0, x_57);
lean_ctor_set(x_70, 1, x_57);
lean_ctor_set(x_70, 2, x_55);
lean_ctor_set(x_70, 3, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_59);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_72, 0, x_47);
lean_ctor_set(x_72, 1, x_47);
lean_ctor_set(x_72, 2, x_48);
lean_ctor_set(x_72, 3, x_49);
lean_ctor_set(x_72, 4, x_52);
lean_ctor_set(x_72, 5, x_56);
lean_ctor_set(x_72, 6, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_46);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_17);
if (x_74 == 0)
{
return x_17;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_17, 0);
x_76 = lean_ctor_get(x_17, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_17);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = lean_mk_string_unchecked("grind", 5, 5);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_main___lam__1), 10, 5);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_11);
lean_closure_set(x_12, 4, x_3);
x_13 = lean_box(0);
x_14 = l_Lean_profileitM___at___Lean_Meta_synthInstance_x3f_spec__3___redArg(x_11, x_10, x_12, x_13, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
lean_dec(x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_logAt___at___Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0_spec__0(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_log___at___Lean_logInfo___at___Lean_Meta_Grind_main_spec__0_spec__0(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___Lean_Meta_Grind_main_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_logInfo___at___Lean_Meta_Grind_main_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_main___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = l_Lean_Meta_Grind_main___lam__0(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
return x_15;
}
}
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_ExposeNames(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Diagnostics(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_RevertAll(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Proj(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Inv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatch(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Split(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Solve(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_SimpUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_ExposeNames(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Diagnostics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Proj(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Inv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EMatch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Split(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Solve(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_SimpUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Cases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
