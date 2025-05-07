// Lean compiler output
// Module: Lean.Meta.Tactic.SolveByElim
// Imports: Init.Data.Sum Lean.LabelAttribute Lean.Meta.Tactic.Apply Lean.Meta.Tactic.Backtrack Lean.Meta.Tactic.Constructor Lean.Meta.Tactic.Repeat Lean.Meta.Tactic.Symm Lean.Elab.Term
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
LEAN_EXPORT lean_object* l_List_filterAuxM___at___Lean_Meta_SolveByElim_applyTactics_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__1_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Iterator_head(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_Meta_Iterator_filterMapM___next(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at___Array_appendList_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Iterator_ofList___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___List_removeAll___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_labelled(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object*, lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_removeAll___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_List_removeAll___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_removeAll___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__4_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_5_(lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_observing_x3f___at_____private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_applySymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___Lean_Meta_SolveByElim_applyTactics_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_exceptEmoji(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__4_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hasMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__6(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___List_removeAll___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_constructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_inferInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_2 = lean_mk_string_unchecked("Meta", 4, 4);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("solveByElim", 11, 11);
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
x_11 = lean_mk_string_unchecked("SolveByElim", 11, 11);
lean_inc(x_11);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("initFn", 6, 6);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = lean_mk_string_unchecked("_@", 2, 2);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = l_Lean_Name_str___override(x_16, x_8);
x_18 = l_Lean_Name_str___override(x_17, x_2);
x_19 = l_Lean_Name_str___override(x_18, x_3);
x_20 = l_Lean_Name_str___override(x_19, x_11);
x_21 = lean_mk_string_unchecked("_hyg", 4, 4);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_unsigned_to_nat(5u);
x_24 = l_Lean_Name_num___override(x_22, x_23);
x_25 = lean_unbox(x_6);
x_26 = l_Lean_registerTraceClass(x_5, x_25, x_24, x_1);
return x_26;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___Lean_Meta_SolveByElim_applyTactics_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_11 = x_1;
} else {
 lean_dec_ref(x_1);
 x_11 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
x_12 = l_Lean_MVarId_inferInstance(x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_9);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_1 = x_10;
x_7 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_23; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_17 = x_12;
} else {
 lean_dec_ref(x_12);
 x_17 = lean_box(0);
}
x_23 = l_Lean_Exception_isInterrupt(x_15);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Exception_isRuntime(x_15);
x_18 = x_24;
goto block_22;
}
else
{
x_18 = x_23;
goto block_22;
}
block_22:
{
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_15);
if (lean_is_scalar(x_11)) {
 x_19 = lean_alloc_ctor(1, 2, 0);
} else {
 x_19 = x_11;
}
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_2);
x_1 = x_10;
x_2 = x_19;
x_7 = x_16;
goto _start;
}
else
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_is_scalar(x_17)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_17;
}
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_mk_string_unchecked("", 0, 0);
x_9 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
x_10 = l_Lean_exceptEmoji(lean_box(0), lean_box(0), x_2);
x_11 = l_Lean_stringToMessageData(x_10);
lean_dec(x_10);
lean_inc(x_9);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_string_unchecked(" trying to apply: ", 18, 18);
x_14 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_MessageData_ofExpr(x_1);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get_uint8(x_10, 0);
x_12 = lean_ctor_get_uint8(x_10, 1);
x_13 = lean_ctor_get_uint8(x_10, 2);
x_14 = lean_ctor_get_uint8(x_10, 3);
x_15 = lean_ctor_get_uint8(x_10, 4);
x_16 = lean_ctor_get_uint8(x_10, 5);
x_17 = lean_ctor_get_uint8(x_10, 6);
x_18 = lean_ctor_get_uint8(x_10, 7);
x_19 = lean_ctor_get_uint8(x_10, 8);
x_20 = lean_ctor_get_uint8(x_10, 10);
x_21 = lean_ctor_get_uint8(x_10, 11);
x_22 = lean_ctor_get_uint8(x_10, 12);
x_23 = lean_ctor_get_uint8(x_10, 13);
x_24 = lean_ctor_get_uint8(x_10, 14);
x_25 = lean_ctor_get_uint8(x_10, 15);
x_26 = lean_ctor_get_uint8(x_10, 16);
x_27 = lean_ctor_get_uint8(x_10, 17);
x_28 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_28, 0, x_11);
lean_ctor_set_uint8(x_28, 1, x_12);
lean_ctor_set_uint8(x_28, 2, x_13);
lean_ctor_set_uint8(x_28, 3, x_14);
lean_ctor_set_uint8(x_28, 4, x_15);
lean_ctor_set_uint8(x_28, 5, x_16);
lean_ctor_set_uint8(x_28, 6, x_17);
lean_ctor_set_uint8(x_28, 7, x_18);
lean_ctor_set_uint8(x_28, 8, x_19);
lean_ctor_set_uint8(x_28, 9, x_1);
lean_ctor_set_uint8(x_28, 10, x_20);
lean_ctor_set_uint8(x_28, 11, x_21);
lean_ctor_set_uint8(x_28, 12, x_22);
lean_ctor_set_uint8(x_28, 13, x_23);
lean_ctor_set_uint8(x_28, 14, x_24);
lean_ctor_set_uint8(x_28, 15, x_25);
lean_ctor_set_uint8(x_28, 16, x_26);
lean_ctor_set_uint8(x_28, 17, x_27);
x_29 = lean_ctor_get_uint64(x_5, sizeof(void*)*7);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_uint64_of_nat(x_30);
x_32 = lean_uint64_shift_right(x_29, x_31);
x_33 = lean_uint64_shift_left(x_32, x_31);
x_34 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_35 = lean_uint64_lor(x_33, x_34);
x_36 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 8);
x_37 = lean_ctor_get(x_5, 1);
x_38 = lean_ctor_get(x_5, 2);
x_39 = lean_ctor_get(x_5, 3);
x_40 = lean_ctor_get(x_5, 4);
x_41 = lean_ctor_get(x_5, 5);
x_42 = lean_ctor_get(x_5, 6);
x_43 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_44 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
x_45 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_45, 0, x_28);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 2, x_38);
lean_ctor_set(x_45, 3, x_39);
lean_ctor_set(x_45, 4, x_40);
lean_ctor_set(x_45, 5, x_41);
lean_ctor_set(x_45, 6, x_42);
lean_ctor_set_uint64(x_45, sizeof(void*)*7, x_35);
lean_ctor_set_uint8(x_45, sizeof(void*)*7 + 8, x_36);
lean_ctor_set_uint8(x_45, sizeof(void*)*7 + 9, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*7 + 10, x_44);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lean_MVarId_apply(x_2, x_3, x_4, x_45, x_6, x_7, x_8, x_9);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_box(0);
x_50 = l_List_filterAuxM___at___Lean_Meta_SolveByElim_applyTactics_spec__0(x_47, x_49, x_5, x_6, x_7, x_8, x_48);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = l_List_reverse___redArg(x_52);
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
x_56 = l_List_reverse___redArg(x_54);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
return x_50;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed), 7, 1);
lean_closure_set(x_10, 0, x_4);
x_11 = lean_box(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed), 9, 4);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_3);
x_13 = lean_mk_string_unchecked("Meta", 4, 4);
x_14 = lean_mk_string_unchecked("Tactic", 6, 6);
x_15 = lean_mk_string_unchecked("solveByElim", 11, 11);
x_16 = l_Lean_Name_mkStr3(x_13, x_14, x_15);
x_17 = lean_box(1);
x_18 = lean_mk_string_unchecked("", 0, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0___boxed), 11, 6);
lean_closure_set(x_19, 0, lean_box(0));
lean_closure_set(x_19, 1, x_16);
lean_closure_set(x_19, 2, x_10);
lean_closure_set(x_19, 3, x_12);
lean_closure_set(x_19, 4, x_17);
lean_closure_set(x_19, 5, x_18);
x_20 = l_Lean_observing_x3f___at_____private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_box(0), x_19, x_5, x_6, x_7, x_8, x_9);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Meta_Iterator_ofList___redArg(x_3, x_5, x_6, x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_box(x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed), 9, 3);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_4);
lean_closure_set(x_13, 2, x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Iterator_filterMapM___next), 9, 4);
lean_closure_set(x_14, 0, lean_box(0));
lean_closure_set(x_14, 1, lean_box(0));
lean_closure_set(x_14, 2, x_13);
lean_closure_set(x_14, 3, x_11);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_box(x_2);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed), 9, 3);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_4);
lean_closure_set(x_18, 2, x_1);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_Iterator_filterMapM___next), 9, 4);
lean_closure_set(x_19, 0, lean_box(0));
lean_closure_set(x_19, 1, lean_box(0));
lean_closure_set(x_19, 2, x_18);
lean_closure_set(x_19, 3, x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SolveByElim_applyTactics___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___Lean_Meta_SolveByElim_applyTactics_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_filterAuxM___at___Lean_Meta_SolveByElim_applyTactics_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_SolveByElim_applyTactics___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Meta_SolveByElim_applyTactics(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Meta_SolveByElim_applyTactics___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Iterator_head(lean_box(0), x_11, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Meta_SolveByElim_applyFirst(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_6(x_13, x_3, x_4, x_5, x_6, x_7, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_box(0);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0), 8, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_5);
lean_ctor_set_uint8(x_10, sizeof(void*)*4, x_9);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 2);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*2 + 1, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*2 + 2, x_14);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 1, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 2, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_7(x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = lean_apply_6(x_2, x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_List_appendTR(lean_box(0), x_16, x_13);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = l_List_appendTR(lean_box(0), x_19, x_13);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_dec(x_13);
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_26 = x_14;
} else {
 lean_dec_ref(x_14);
 x_26 = lean_box(0);
}
x_32 = l_Lean_Exception_isInterrupt(x_24);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Exception_isRuntime(x_24);
x_27 = x_33;
goto block_31;
}
else
{
x_27 = x_32;
goto block_31;
}
block_31:
{
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_26);
lean_dec(x_24);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_apply_7(x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_26)) {
 x_30 = lean_alloc_ctor(1, 2, 0);
} else {
 x_30 = x_26;
}
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0), 9, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 3);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*4, x_9);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 2);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*2 + 1, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*2 + 2, x_14);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 1, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 2, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_Meta_intro1Core(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed), 6, 0);
x_3 = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
lean_inc(x_3);
x_11 = l_Lean_Meta_synthInstance(x_8, x_10, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_12, x_3, x_13);
lean_dec(x_3);
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
uint8_t x_21; 
lean_dec(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0), 6, 0);
x_3 = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_16 = l_Lean_Exception_isInterrupt(x_10);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_Exception_isRuntime(x_10);
lean_dec(x_10);
x_12 = x_17;
goto block_15;
}
else
{
lean_dec(x_10);
x_12 = x_16;
goto block_15;
}
block_15:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_6(x_13, x_3, x_4, x_5, x_6, x_7, x_11);
return x_14;
}
else
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0), 8, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_5);
lean_ctor_set_uint8(x_10, sizeof(void*)*4, x_9);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 2);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*2 + 1, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*2 + 2, x_14);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 1, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 2, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_Meta_intro1Core(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_9);
if (x_23 == 0)
{
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed), 6, 0);
x_3 = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_7 = lean_box(2);
x_8 = lean_box(1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 0, 4);
x_11 = lean_unbox(x_7);
lean_ctor_set_uint8(x_10, 0, x_11);
x_12 = lean_unbox(x_8);
lean_ctor_set_uint8(x_10, 1, x_12);
x_13 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, 2, x_13);
x_14 = lean_unbox(x_8);
lean_ctor_set_uint8(x_10, 3, x_14);
x_15 = l_Lean_MVarId_constructor(x_1, x_10, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed), 6, 0);
x_3 = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
lean_inc(x_3);
x_11 = l_Lean_Meta_synthInstance(x_8, x_10, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_12, x_3, x_13);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0), 6, 0);
x_3 = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_13 = l_Lean_Expr_mvar___override(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___boxed), 6, 1);
lean_closure_set(x_14, 0, x_13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_11, x_14, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_16);
{
lean_object* _tmp_0 = x_12;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_17;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
else
{
uint8_t x_19; 
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
lean_inc(x_23);
x_25 = l_Lean_Expr_mvar___override(x_23);
x_26 = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___boxed), 6, 1);
lean_closure_set(x_26, 0, x_25);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_27 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_23, x_26, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_2);
x_1 = x_24;
x_2 = x_30;
x_7 = x_29;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_34 = x_27;
} else {
 lean_dec_ref(x_27);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_11 = l_List_mapM_loop___at___Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(x_3, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = lean_apply_6(x_1, x_12, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_mk_string_unchecked("failed", 6, 6);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_19, x_5, x_6, x_7, x_8, x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_apply_7(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
return x_11;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0), 9, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 3);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*4, x_9);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 2);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*2 + 1, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*2 + 2, x_14);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 1, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 2, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM_loop___at___Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Expr_hasMVar___boxed), 1, 0);
lean_inc(x_2);
x_9 = l_List_any___redArg(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0), 7, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_occurs(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_List_any___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1___boxed), 2, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_List_all___redArg(x_1, x_8);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2___boxed), 7, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (x_12 == 0)
{
x_2 = x_1;
goto block_11;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_15 = lean_box(0);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_14);
x_18 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 1, x_18);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 2, x_16);
x_19 = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(x_17);
x_2 = x_19;
goto block_11;
}
block_11:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*1 + 1, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1 + 2, x_9);
x_10 = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(x_8);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_10 = l_List_reverse___redArg(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = lean_apply_7(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_16);
{
lean_object* _tmp_0 = x_14;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_8 = x_17;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_9 = _tmp_8;
}
goto _start;
}
else
{
uint8_t x_19; 
lean_free_object(x_1);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = lean_apply_7(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_2);
x_1 = x_24;
x_2 = x_28;
x_9 = x_27;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_32 = x_25;
} else {
 lean_dec_ref(x_25);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = lean_apply_8(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = l_List_mapM_loop___at___Lean_Meta_SolveByElim_elabContextLemmas_spec__0(x_3, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_List_appendTR(lean_box(0), x_12, x_17);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = l_List_appendTR(lean_box(0), x_12, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_dec(x_12);
return x_15;
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
return x_11;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_TermElabM_run___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
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
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0), 10, 3);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_3);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_box(1);
x_14 = lean_box(0);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_unsigned_to_nat(5u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_to_nat(x_18);
x_20 = lean_nat_pow(x_16, x_19);
lean_dec(x_19);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = lean_usize_to_nat(x_21);
x_23 = lean_mk_empty_array_with_capacity(x_22);
lean_dec(x_22);
lean_inc(x_23);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_25);
lean_ctor_set(x_26, 3, x_25);
lean_ctor_set_usize(x_26, 4, x_18);
x_27 = lean_box(0);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_29, 0, x_11);
lean_ctor_set(x_29, 1, x_12);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_15);
lean_ctor_set(x_29, 4, x_27);
lean_ctor_set(x_29, 5, x_27);
lean_ctor_set(x_29, 6, x_28);
x_30 = lean_unbox(x_13);
lean_ctor_set_uint8(x_29, sizeof(void*)*7, x_30);
x_31 = lean_unbox(x_13);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 1, x_31);
x_32 = lean_unbox(x_14);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 2, x_32);
x_33 = lean_unbox(x_13);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 3, x_33);
x_34 = lean_unbox(x_13);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 4, x_34);
x_35 = lean_unbox(x_14);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 5, x_35);
x_36 = lean_unbox(x_14);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 6, x_36);
x_37 = lean_unbox(x_14);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 7, x_37);
x_38 = lean_unbox(x_13);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 8, x_38);
x_39 = lean_unbox(x_14);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 9, x_39);
x_40 = lean_unbox(x_13);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 10, x_40);
x_41 = lean_box(0);
x_42 = lean_box(0);
x_43 = lean_box(0);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_27);
lean_ctor_set(x_45, 2, x_41);
lean_ctor_set(x_45, 3, x_42);
lean_ctor_set(x_45, 4, x_43);
lean_ctor_set(x_45, 5, x_27);
lean_ctor_set(x_45, 6, x_44);
x_46 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed), 8, 3);
lean_closure_set(x_46, 0, x_10);
lean_closure_set(x_46, 1, x_29);
lean_closure_set(x_46, 2, x_45);
x_47 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_2, x_46, x_5, x_6, x_7, x_8, x_9);
return x_47;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SolveByElim_elabContextLemmas(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_10 = l_Lean_Meta_SolveByElim_elabContextLemmas(x_1, x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec(x_13);
x_16 = l_Lean_Meta_SolveByElim_applyTactics___redArg(x_14, x_15, x_11, x_4, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SolveByElim_applyLemmas(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_10 = l_Lean_Meta_SolveByElim_elabContextLemmas(x_1, x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec(x_13);
x_16 = l_Lean_Meta_SolveByElim_applyFirst(x_14, x_15, x_11, x_4, x_5, x_6, x_7, x_8, x_12);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_List_foldl___at___Array_appendList_spec__0(lean_box(0), x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_4 = x_15;
x_5 = x_16;
goto _start;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
x_21 = l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0(x_19, x_7, x_8, x_9, x_10, x_11);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_21, 1);
x_26 = lean_ctor_get(x_21, 0);
lean_dec(x_26);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_eq(x_2, x_27);
if (x_28 == 1)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_array_push(x_6, x_19);
x_30 = l_List_foldl___at___Array_appendList_spec__0(lean_box(0), x_29, x_20);
x_31 = l_List_foldl___at___Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__0_spec__0(x_30, x_5);
x_32 = lean_box(x_3);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_21, 0, x_33);
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_free_object(x_21);
lean_inc(x_1);
lean_inc(x_19);
x_34 = lean_apply_1(x_1, x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_35 = l_Lean_observing_x3f___at_____private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_box(0), x_34, x_7, x_8, x_9, x_10, x_25);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_sub(x_2, x_38);
lean_dec(x_2);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_40; 
lean_free_object(x_4);
x_40 = lean_array_push(x_6, x_19);
x_2 = x_39;
x_4 = x_20;
x_6 = x_40;
x_11 = x_37;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_19);
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
lean_dec(x_36);
x_43 = lean_box(1);
lean_ctor_set(x_4, 1, x_5);
lean_ctor_set(x_4, 0, x_20);
x_44 = lean_unbox(x_43);
{
lean_object* _tmp_1 = x_39;
uint8_t _tmp_2 = x_44;
lean_object* _tmp_3 = x_42;
lean_object* _tmp_4 = x_4;
lean_object* _tmp_10 = x_37;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_11 = _tmp_10;
}
goto _start;
}
}
else
{
uint8_t x_46; 
lean_free_object(x_4);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_35);
if (x_46 == 0)
{
return x_35;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_35, 0);
x_48 = lean_ctor_get(x_35, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_35);
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
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_21, 1);
lean_inc(x_50);
lean_dec(x_21);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_eq(x_2, x_51);
if (x_52 == 1)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_free_object(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_array_push(x_6, x_19);
x_54 = l_List_foldl___at___Array_appendList_spec__0(lean_box(0), x_53, x_20);
x_55 = l_List_foldl___at___Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__0_spec__0(x_54, x_5);
x_56 = lean_box(x_3);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_50);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_inc(x_1);
lean_inc(x_19);
x_59 = lean_apply_1(x_1, x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_60 = l_Lean_observing_x3f___at_____private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_box(0), x_59, x_7, x_8, x_9, x_10, x_50);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_sub(x_2, x_63);
lean_dec(x_2);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_65; 
lean_free_object(x_4);
x_65 = lean_array_push(x_6, x_19);
x_2 = x_64;
x_4 = x_20;
x_6 = x_65;
x_11 = x_62;
goto _start;
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_19);
x_67 = lean_ctor_get(x_61, 0);
lean_inc(x_67);
lean_dec(x_61);
x_68 = lean_box(1);
lean_ctor_set(x_4, 1, x_5);
lean_ctor_set(x_4, 0, x_20);
x_69 = lean_unbox(x_68);
{
lean_object* _tmp_1 = x_64;
uint8_t _tmp_2 = x_69;
lean_object* _tmp_3 = x_67;
lean_object* _tmp_4 = x_4;
lean_object* _tmp_10 = x_62;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_11 = _tmp_10;
}
goto _start;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_free_object(x_4);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_71 = lean_ctor_get(x_60, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_60, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_73 = x_60;
} else {
 lean_dec_ref(x_60);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
}
else
{
lean_object* x_75; 
lean_free_object(x_4);
lean_dec(x_19);
x_75 = lean_ctor_get(x_21, 1);
lean_inc(x_75);
lean_dec(x_21);
x_4 = x_20;
x_11 = x_75;
goto _start;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_77 = lean_ctor_get(x_4, 0);
x_78 = lean_ctor_get(x_4, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_4);
x_79 = l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0(x_77, x_7, x_8, x_9, x_10, x_11);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_83 = x_79;
} else {
 lean_dec_ref(x_79);
 x_83 = lean_box(0);
}
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_nat_dec_eq(x_2, x_84);
if (x_85 == 1)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_86 = lean_array_push(x_6, x_77);
x_87 = l_List_foldl___at___Array_appendList_spec__0(lean_box(0), x_86, x_78);
x_88 = l_List_foldl___at___Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__0_spec__0(x_87, x_5);
x_89 = lean_box(x_3);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
if (lean_is_scalar(x_83)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_83;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_82);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_83);
lean_inc(x_1);
lean_inc(x_77);
x_92 = lean_apply_1(x_1, x_77);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_93 = l_Lean_observing_x3f___at_____private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_box(0), x_92, x_7, x_8, x_9, x_10, x_82);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_sub(x_2, x_96);
lean_dec(x_2);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_98; 
x_98 = lean_array_push(x_6, x_77);
x_2 = x_97;
x_4 = x_78;
x_6 = x_98;
x_11 = x_95;
goto _start;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_dec(x_77);
x_100 = lean_ctor_get(x_94, 0);
lean_inc(x_100);
lean_dec(x_94);
x_101 = lean_box(1);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_78);
lean_ctor_set(x_102, 1, x_5);
x_103 = lean_unbox(x_101);
x_2 = x_97;
x_3 = x_103;
x_4 = x_100;
x_5 = x_102;
x_11 = x_95;
goto _start;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_109; 
lean_dec(x_77);
x_109 = lean_ctor_get(x_79, 1);
lean_inc(x_109);
lean_dec(x_79);
x_4 = x_78;
x_11 = x_109;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_eq(x_2, x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_array_uget(x_1, x_2);
x_22 = l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0(x_18, x_5, x_6, x_7, x_8, x_9);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_19 = x_25;
goto block_21;
}
else
{
lean_object* x_26; 
lean_dec(x_18);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_10 = x_4;
x_11 = x_26;
goto block_16;
}
block_21:
{
lean_object* x_20; 
x_20 = lean_array_push(x_4, x_18);
x_10 = x_20;
x_11 = x_19;
goto block_16;
}
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
block_16:
{
lean_object* x_12; size_t x_13; size_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_10;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_box(0);
x_10 = lean_box(0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_mk_empty_array_with_capacity(x_11);
x_13 = lean_unbox(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_12);
x_14 = l_Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__0(x_1, x_3, x_13, x_2, x_10, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_27; uint8_t x_28; 
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
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_20 = x_15;
} else {
 lean_dec_ref(x_15);
 x_20 = lean_box(0);
}
x_27 = lean_array_get_size(x_19);
x_28 = lean_nat_dec_lt(x_11, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = x_12;
x_22 = x_16;
goto block_26;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = x_12;
x_22 = x_16;
goto block_26;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_usize_of_nat(x_11);
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(x_19, x_30, x_31, x_12, x_4, x_5, x_6, x_7, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_21 = x_33;
x_22 = x_34;
goto block_26;
}
}
block_26:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_array_to_list(x_21);
if (lean_is_scalar(x_20)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_20;
}
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
if (lean_is_scalar(x_17)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_17;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_35; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_14, 0);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_14);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_mk_string_unchecked("repeat1' made no progress", 25, 25);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_15, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_9);
if (x_23 == 0)
{
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyFirstLemma), 9, 3);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0(x_11, x_4, x_14, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_mk_string_unchecked("Meta", 4, 4);
x_19 = lean_mk_string_unchecked("Tactic", 6, 6);
x_20 = lean_mk_string_unchecked("solveByElim", 11, 11);
x_21 = l_Lean_Name_mkStr3(x_18, x_19, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyLemmas___boxed), 9, 3);
lean_closure_set(x_22, 0, x_3);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_2);
x_23 = l_Lean_Meta_Tactic_Backtrack_backtrack(x_17, x_21, x_22, x_4, x_5, x_6, x_7, x_8, x_9);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Meta_repeat_x27Core_go___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__0(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_repeat_x27Core___at___Lean_Meta_repeat1_x27___at___Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_mk_string_unchecked("⏮️ starting over using `exfalso`", 36, 32);
x_8 = l_Lean_stringToMessageData(x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_11 = l_Lean_MVarId_exfalso(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_2);
x_15 = l_Lean_Meta_SolveByElim_solveByElim_run(x_3, x_4, x_5, x_14, x_6, x_7, x_8, x_9, x_13);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Meta_SolveByElim_solveByElim_run(x_2, x_3, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_28; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed), 6, 0);
x_28 = l_Lean_Exception_isInterrupt(x_12);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Exception_isRuntime(x_12);
lean_dec(x_12);
x_15 = x_29;
goto block_27;
}
else
{
lean_dec(x_12);
x_15 = x_28;
goto block_27;
}
block_27:
{
if (x_15 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*2 + 2);
lean_dec(x_17);
if (x_18 == 0)
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_solveByElim___lam__1), 10, 5);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_16);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_3);
lean_closure_set(x_20, 4, x_10);
x_21 = lean_mk_string_unchecked("Meta", 4, 4);
x_22 = lean_mk_string_unchecked("Tactic", 6, 6);
x_23 = lean_mk_string_unchecked("solveByElim", 11, 11);
x_24 = l_Lean_Name_mkStr3(x_21, x_22, x_23);
x_25 = lean_mk_string_unchecked("", 0, 0);
x_26 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_24, x_14, x_20, x_18, x_25, x_5, x_6, x_7, x_8, x_13);
return x_26;
}
}
else
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
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
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SolveByElim_solveByElim___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Expr_applySymm(x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_12;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_24; 
lean_free_object(x_1);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_19 = x_13;
} else {
 lean_dec_ref(x_13);
 x_19 = lean_box(0);
}
x_24 = l_Lean_Exception_isInterrupt(x_17);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Exception_isRuntime(x_17);
x_20 = x_25;
goto block_23;
}
else
{
x_20 = x_24;
goto block_23;
}
block_23:
{
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
x_1 = x_12;
x_7 = x_18;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_19)) {
 x_22 = lean_alloc_ctor(1, 2, 0);
} else {
 x_22 = x_19;
}
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_28 = l_Lean_Expr_applySymm(x_26, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_2);
x_1 = x_27;
x_2 = x_31;
x_7 = x_30;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_40; 
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_35 = x_28;
} else {
 lean_dec_ref(x_28);
 x_35 = lean_box(0);
}
x_40 = l_Lean_Exception_isInterrupt(x_33);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = l_Lean_Exception_isRuntime(x_33);
x_36 = x_41;
goto block_39;
}
else
{
x_36 = x_40;
goto block_39;
}
block_39:
{
if (x_36 == 0)
{
lean_dec(x_35);
lean_dec(x_33);
x_1 = x_27;
x_7 = x_34;
goto _start;
}
else
{
lean_object* x_38; 
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_35)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_35;
}
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_1 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
lean_inc(x_2);
x_10 = l_List_filterMapM_loop___at___Lean_Meta_SolveByElim_saturateSymm_spec__0(x_2, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_List_appendTR(lean_box(0), x_2, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l_List_appendTR(lean_box(0), x_2, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_dec(x_2);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Meta_SolveByElim_saturateSymm(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_16);
x_17 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0(x_1, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
lean_dec(x_16);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_usize_of_nat(x_31);
x_33 = lean_usize_add(x_4, x_32);
x_4 = x_33;
x_5 = x_30;
x_12 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__1_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_17; 
x_8 = lean_box(0);
x_17 = lean_array_uget(x_1, x_3);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_dec(x_4);
x_9 = x_18;
x_10 = x_5;
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_LocalDecl_isImplementationDetail(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_LocalDecl_toExpr(x_20);
x_23 = lean_array_push(x_19, x_22);
x_9 = x_23;
x_10 = x_5;
goto block_16;
}
else
{
lean_dec(x_20);
x_9 = x_19;
x_10 = x_5;
goto block_16;
}
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
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__1_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; 
x_14 = lean_box(0);
x_23 = lean_array_uget(x_1, x_3);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
x_15 = x_24;
x_16 = x_11;
goto block_22;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_LocalDecl_isImplementationDetail(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_LocalDecl_toExpr(x_26);
x_29 = lean_array_push(x_25, x_28);
x_15 = x_29;
x_16 = x_11;
goto block_22;
}
else
{
lean_dec(x_26);
x_15 = x_25;
x_16 = x_11;
goto block_22;
}
}
block_22:
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_3, x_19);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_20, x_17, x_16);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
x_15 = lean_array_size(x_12);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_usize_of_nat(x_16);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__0(x_1, x_12, x_15, x_17, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_23);
lean_ctor_set(x_18, 0, x_2);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_19);
lean_free_object(x_2);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_18, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_29);
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec(x_18);
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
lean_dec(x_20);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
lean_dec(x_2);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
x_36 = lean_array_size(x_33);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_usize_of_nat(x_37);
x_39 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__0(x_1, x_33, x_36, x_38, x_35, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_33);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
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
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_40);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_48 = x_39;
} else {
 lean_dec_ref(x_39);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
lean_dec(x_41);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_2);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; lean_object* x_56; size_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_2, 0);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_3);
x_55 = lean_array_size(x_52);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_usize_of_nat(x_56);
x_58 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__1(x_52, x_55, x_57, x_54, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_52);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_58);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_58, 0);
lean_dec(x_62);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
lean_ctor_set(x_2, 0, x_63);
lean_ctor_set(x_58, 0, x_2);
return x_58;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_dec(x_59);
lean_ctor_set(x_2, 0, x_65);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_2);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_59);
lean_free_object(x_2);
x_67 = !lean_is_exclusive(x_58);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_58, 0);
lean_dec(x_68);
x_69 = lean_ctor_get(x_60, 0);
lean_inc(x_69);
lean_dec(x_60);
lean_ctor_set(x_58, 0, x_69);
return x_58;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_58, 1);
lean_inc(x_70);
lean_dec(x_58);
x_71 = lean_ctor_get(x_60, 0);
lean_inc(x_71);
lean_dec(x_60);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; size_t x_76; lean_object* x_77; size_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_73 = lean_ctor_get(x_2, 0);
lean_inc(x_73);
lean_dec(x_2);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_3);
x_76 = lean_array_size(x_73);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_usize_of_nat(x_77);
x_79 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__1(x_73, x_76, x_78, x_75, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_73);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_83 = x_79;
} else {
 lean_dec_ref(x_79);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec(x_80);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
if (lean_is_scalar(x_83)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_83;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_82);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_80);
x_87 = lean_ctor_get(x_79, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_88 = x_79;
} else {
 lean_dec_ref(x_79);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_81, 0);
lean_inc(x_89);
lean_dec(x_81);
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
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__4_spec__4___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_17; 
x_8 = lean_box(0);
x_17 = lean_array_uget(x_1, x_3);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_dec(x_4);
x_9 = x_18;
x_10 = x_5;
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_LocalDecl_isImplementationDetail(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_LocalDecl_toExpr(x_20);
x_23 = lean_array_push(x_19, x_22);
x_9 = x_23;
x_10 = x_5;
goto block_16;
}
else
{
lean_dec(x_20);
x_9 = x_19;
x_10 = x_5;
goto block_16;
}
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
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__4_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__4_spec__4___redArg(x_1, x_2, x_3, x_4, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; 
x_14 = lean_box(0);
x_23 = lean_array_uget(x_1, x_3);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
x_15 = x_24;
x_16 = x_11;
goto block_22;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_LocalDecl_isImplementationDetail(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_LocalDecl_toExpr(x_26);
x_29 = lean_array_push(x_25, x_28);
x_15 = x_29;
x_16 = x_11;
goto block_22;
}
else
{
lean_dec(x_26);
x_15 = x_25;
x_16 = x_11;
goto block_22;
}
}
block_22:
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_3, x_19);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__4_spec__4___redArg(x_1, x_2, x_20, x_17, x_16);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_inc(x_2);
x_11 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0(x_2, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_array_size(x_21);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_usize_of_nat(x_25);
x_27 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__4(x_21, x_24, x_26, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_21);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_28);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_27, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_38);
return x_27;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_dec(x_27);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0(x_11, x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_1 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_5);
x_10 = l_Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*2 + 1);
x_15 = lean_array_to_list(x_11);
x_16 = l_Lean_Meta_SolveByElim_saturateSymm(x_14, x_15, x_5, x_6, x_7, x_8, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_box(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_MVarId_applyRules___lam__0___boxed), 9, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_box(0);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
lean_inc(x_12);
x_16 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_16, 0, x_12);
x_17 = lean_unbox(x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 1, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 2, x_15);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_SolveByElim_solveByElim(x_16, x_2, x_11, x_19, x_5, x_6, x_7, x_8, x_9);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__1_spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0_spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__4_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__4_spec__4___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__4_spec__4(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0_spec__4(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_MVarId_applyRules___lam__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_MVarId_applyRules(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_box(0);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_12 = lean_unbox(x_10);
x_13 = l_Lean_Elab_Term_elabTerm(x_1, x_9, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = l_Lean_Syntax_getId(x_9);
lean_dec(x_9);
x_11 = l_Lean_labelled(x_10, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_15, x_2, x_12);
x_2 = x_18;
x_3 = x_19;
x_6 = x_13;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapMUnsafe_map___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(x_1, x_2, x_3, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = l_List_reverse___redArg(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l_Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_16);
{
lean_object* _tmp_0 = x_14;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_8 = x_17;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_9 = _tmp_8;
}
goto _start;
}
else
{
uint8_t x_19; 
lean_free_object(x_1);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = l_Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_2);
x_1 = x_24;
x_2 = x_28;
x_9 = x_27;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_32 = x_25;
} else {
 lean_dec_ref(x_25);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___List_removeAll___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_expr_eqv(x_1, x_5);
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
LEAN_EXPORT uint8_t l_List_removeAll___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_List_elem___at___List_removeAll___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(x_2, x_1);
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
LEAN_EXPORT lean_object* l_List_removeAll___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_List_removeAll___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_List_filter___redArg(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed), 8, 1);
lean_closure_set(x_7, 0, x_5);
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
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed), 8, 1);
lean_closure_set(x_11, 0, x_9);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_alloc_closure((void*)(l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___lam__0___boxed), 8, 1);
lean_closure_set(x_7, 0, x_5);
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
x_11 = lean_alloc_closure((void*)(l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___lam__0___boxed), 8, 1);
lean_closure_set(x_11, 0, x_9);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Array_append(lean_box(0), x_4, x_6);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_2 == 0)
{
goto block_24;
}
else
{
if (x_3 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_11);
return x_26;
}
else
{
goto block_24;
}
}
block_24:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_7);
x_12 = l_Lean_getLocalHyps___at___Lean_MVarId_applyRules_spec__0(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l_List_mapM_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(x_1, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*2 + 1);
x_21 = lean_array_to_list(x_13);
x_22 = l_List_removeAll___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(x_21, x_17);
x_23 = l_Lean_Meta_SolveByElim_saturateSymm(x_20, x_22, x_7, x_8, x_9, x_10, x_18);
return x_23;
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_33 = lean_box(x_1);
x_34 = lean_box(x_2);
lean_inc(x_4);
x_35 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed), 11, 3);
lean_closure_set(x_35, 0, x_4);
lean_closure_set(x_35, 1, x_33);
lean_closure_set(x_35, 2, x_34);
if (x_2 == 0)
{
x_52 = x_6;
x_53 = x_7;
x_54 = x_8;
x_55 = x_9;
x_56 = x_10;
goto block_671;
}
else
{
if (x_1 == 0)
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; uint8_t x_675; 
lean_dec(x_35);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_672 = lean_mk_string_unchecked("It doesn't make sense to use `*` without `only`.", 48, 48);
x_673 = l_Lean_stringToMessageData(x_672);
lean_dec(x_672);
x_674 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_673, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
x_675 = !lean_is_exclusive(x_674);
if (x_675 == 0)
{
return x_674;
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; 
x_676 = lean_ctor_get(x_674, 0);
x_677 = lean_ctor_get(x_674, 1);
lean_inc(x_677);
lean_inc(x_676);
lean_dec(x_674);
x_678 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_678, 0, x_676);
lean_ctor_set(x_678, 1, x_677);
return x_678;
}
}
else
{
x_52 = x_6;
x_53 = x_7;
x_54 = x_8;
x_55 = x_9;
x_56 = x_10;
goto block_671;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
block_32:
{
uint8_t x_24; 
x_24 = l_List_isEmpty___redArg(x_4);
lean_dec(x_4);
if (x_24 == 0)
{
if (x_1 == 0)
{
lean_dec(x_22);
x_11 = x_23;
x_12 = x_20;
x_13 = x_21;
goto block_16;
}
else
{
if (x_2 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_23);
lean_dec(x_20);
x_25 = lean_mk_string_unchecked("It doesn't make sense to remove local hypotheses when using `only` without `*`.", 79, 79);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_26, x_17, x_18, x_22, x_19, x_21);
lean_dec(x_22);
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
else
{
lean_dec(x_22);
x_11 = x_23;
x_12 = x_20;
x_13 = x_21;
goto block_16;
}
}
}
else
{
lean_dec(x_22);
x_11 = x_23;
x_12 = x_20;
x_13 = x_21;
goto block_16;
}
}
block_51:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_array_to_list(x_43);
lean_inc(x_39);
x_45 = l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(x_44, x_39);
if (x_1 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(x_3, x_39);
x_47 = l_List_appendTR(lean_box(0), x_46, x_45);
x_48 = l_List_appendTR(lean_box(0), x_47, x_42);
x_17 = x_36;
x_18 = x_37;
x_19 = x_38;
x_20 = x_35;
x_21 = x_40;
x_22 = x_41;
x_23 = x_48;
goto block_32;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_42);
x_49 = l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(x_3, x_39);
x_50 = l_List_appendTR(lean_box(0), x_49, x_45);
x_17 = x_36;
x_18 = x_37;
x_19 = x_38;
x_20 = x_35;
x_21 = x_40;
x_22 = x_41;
x_23 = x_50;
goto block_32;
}
}
block_671:
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_st_ref_get(x_55, x_56);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(x_52, x_53, x_54, x_55, x_60);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
x_66 = lean_st_ref_get(x_55, x_65);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 1);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(x_52, x_53, x_54, x_55, x_69);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
x_75 = lean_st_ref_get(x_55, x_74);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(x_52, x_53, x_54, x_55, x_78);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = lean_ctor_get(x_80, 1);
x_84 = lean_st_ref_get(x_55, x_83);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; size_t x_123; lean_object* x_124; size_t x_125; lean_object* x_126; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_ctor_get(x_84, 1);
x_88 = lean_ctor_get(x_54, 5);
lean_inc(x_88);
x_89 = lean_box(0);
x_90 = l_Lean_Environment_mainModule(x_61);
lean_dec(x_61);
x_91 = lean_mk_string_unchecked("rfl", 3, 3);
lean_inc(x_91);
x_92 = l_Lean_Name_mkStr1(x_91);
x_93 = lean_box(0);
lean_inc(x_92);
lean_ctor_set_tag(x_84, 1);
lean_ctor_set(x_84, 1, x_93);
lean_ctor_set(x_84, 0, x_92);
x_94 = l_Lean_Environment_mainModule(x_70);
lean_dec(x_70);
x_95 = lean_mk_string_unchecked("trivial", 7, 7);
lean_inc(x_95);
x_96 = l_Lean_Name_mkStr1(x_95);
lean_inc(x_96);
lean_ctor_set_tag(x_80, 1);
lean_ctor_set(x_80, 1, x_93);
lean_ctor_set(x_80, 0, x_96);
x_97 = l_Lean_Environment_mainModule(x_79);
lean_dec(x_79);
x_98 = lean_mk_string_unchecked("congrFun", 8, 8);
lean_inc(x_98);
x_99 = l_Lean_Name_mkStr1(x_98);
lean_inc(x_99);
lean_ctor_set_tag(x_75, 1);
lean_ctor_set(x_75, 1, x_93);
lean_ctor_set(x_75, 0, x_99);
x_100 = lean_unbox(x_89);
x_101 = l_Lean_SourceInfo_fromRef(x_88, x_100);
lean_dec(x_88);
x_102 = lean_ctor_get(x_54, 10);
lean_inc(x_102);
x_103 = l_String_toSubstring_x27(x_91);
lean_inc(x_102);
x_104 = l_Lean_addMacroScope(x_90, x_92, x_102);
x_105 = lean_box(0);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 1, x_105);
lean_ctor_set(x_71, 0, x_84);
x_106 = l_String_toSubstring_x27(x_95);
lean_inc(x_102);
x_107 = l_Lean_addMacroScope(x_94, x_96, x_102);
lean_ctor_set_tag(x_66, 1);
lean_ctor_set(x_66, 1, x_105);
lean_ctor_set(x_66, 0, x_80);
x_108 = l_String_toSubstring_x27(x_98);
lean_inc(x_102);
x_109 = l_Lean_addMacroScope(x_97, x_99, x_102);
lean_ctor_set_tag(x_62, 1);
lean_ctor_set(x_62, 1, x_105);
lean_ctor_set(x_62, 0, x_75);
x_110 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_110, 0, x_64);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set(x_110, 2, x_107);
lean_ctor_set(x_110, 3, x_66);
x_111 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_111, 0, x_73);
lean_ctor_set(x_111, 1, x_108);
lean_ctor_set(x_111, 2, x_109);
lean_ctor_set(x_111, 3, x_62);
x_112 = lean_ctor_get(x_86, 0);
lean_inc(x_112);
lean_dec(x_86);
x_113 = l_Lean_Environment_mainModule(x_112);
lean_dec(x_112);
x_114 = lean_mk_string_unchecked("congrArg", 8, 8);
lean_inc(x_114);
x_115 = l_String_toSubstring_x27(x_114);
x_116 = l_Lean_Name_mkStr1(x_114);
lean_inc(x_116);
x_117 = l_Lean_addMacroScope(x_113, x_116, x_102);
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 1, x_93);
lean_ctor_set(x_57, 0, x_116);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_57);
lean_ctor_set(x_118, 1, x_105);
x_119 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_119, 0, x_82);
lean_ctor_set(x_119, 1, x_115);
lean_ctor_set(x_119, 2, x_117);
lean_ctor_set(x_119, 3, x_118);
x_120 = lean_box(0);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_111);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_array_size(x_5);
x_124 = lean_unsigned_to_nat(0u);
x_125 = lean_usize_of_nat(x_124);
x_126 = l_Array_mapMUnsafe_map___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(x_123, x_125, x_5, x_54, x_55, x_87);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_129, 0, x_101);
lean_ctor_set(x_129, 1, x_103);
lean_ctor_set(x_129, 2, x_104);
lean_ctor_set(x_129, 3, x_71);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_110);
lean_ctor_set(x_130, 1, x_122);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_box(0);
x_133 = l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(x_131, x_132);
x_134 = l_Array_empty(lean_box(0));
x_135 = lean_array_get_size(x_127);
x_136 = lean_nat_dec_lt(x_124, x_135);
if (x_136 == 0)
{
lean_dec(x_135);
lean_dec(x_127);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_132;
x_40 = x_128;
x_41 = x_54;
x_42 = x_133;
x_43 = x_134;
goto block_51;
}
else
{
uint8_t x_137; 
x_137 = lean_nat_dec_le(x_135, x_135);
if (x_137 == 0)
{
lean_dec(x_135);
lean_dec(x_127);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_132;
x_40 = x_128;
x_41 = x_54;
x_42 = x_133;
x_43 = x_134;
goto block_51;
}
else
{
size_t x_138; lean_object* x_139; 
x_138 = lean_usize_of_nat(x_135);
lean_dec(x_135);
x_139 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__6(x_127, x_125, x_138, x_134);
lean_dec(x_127);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_132;
x_40 = x_128;
x_41 = x_54;
x_42 = x_133;
x_43 = x_139;
goto block_51;
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_122);
lean_dec(x_110);
lean_dec(x_71);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_54);
lean_dec(x_35);
lean_dec(x_4);
lean_dec(x_3);
x_140 = !lean_is_exclusive(x_126);
if (x_140 == 0)
{
return x_126;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_126, 0);
x_142 = lean_ctor_get(x_126, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_126);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; size_t x_182; lean_object* x_183; size_t x_184; lean_object* x_185; 
x_144 = lean_ctor_get(x_84, 0);
x_145 = lean_ctor_get(x_84, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_84);
x_146 = lean_ctor_get(x_54, 5);
lean_inc(x_146);
x_147 = lean_box(0);
x_148 = l_Lean_Environment_mainModule(x_61);
lean_dec(x_61);
x_149 = lean_mk_string_unchecked("rfl", 3, 3);
lean_inc(x_149);
x_150 = l_Lean_Name_mkStr1(x_149);
x_151 = lean_box(0);
lean_inc(x_150);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = l_Lean_Environment_mainModule(x_70);
lean_dec(x_70);
x_154 = lean_mk_string_unchecked("trivial", 7, 7);
lean_inc(x_154);
x_155 = l_Lean_Name_mkStr1(x_154);
lean_inc(x_155);
lean_ctor_set_tag(x_80, 1);
lean_ctor_set(x_80, 1, x_151);
lean_ctor_set(x_80, 0, x_155);
x_156 = l_Lean_Environment_mainModule(x_79);
lean_dec(x_79);
x_157 = lean_mk_string_unchecked("congrFun", 8, 8);
lean_inc(x_157);
x_158 = l_Lean_Name_mkStr1(x_157);
lean_inc(x_158);
lean_ctor_set_tag(x_75, 1);
lean_ctor_set(x_75, 1, x_151);
lean_ctor_set(x_75, 0, x_158);
x_159 = lean_unbox(x_147);
x_160 = l_Lean_SourceInfo_fromRef(x_146, x_159);
lean_dec(x_146);
x_161 = lean_ctor_get(x_54, 10);
lean_inc(x_161);
x_162 = l_String_toSubstring_x27(x_149);
lean_inc(x_161);
x_163 = l_Lean_addMacroScope(x_148, x_150, x_161);
x_164 = lean_box(0);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 1, x_164);
lean_ctor_set(x_71, 0, x_152);
x_165 = l_String_toSubstring_x27(x_154);
lean_inc(x_161);
x_166 = l_Lean_addMacroScope(x_153, x_155, x_161);
lean_ctor_set_tag(x_66, 1);
lean_ctor_set(x_66, 1, x_164);
lean_ctor_set(x_66, 0, x_80);
x_167 = l_String_toSubstring_x27(x_157);
lean_inc(x_161);
x_168 = l_Lean_addMacroScope(x_156, x_158, x_161);
lean_ctor_set_tag(x_62, 1);
lean_ctor_set(x_62, 1, x_164);
lean_ctor_set(x_62, 0, x_75);
x_169 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_169, 0, x_64);
lean_ctor_set(x_169, 1, x_165);
lean_ctor_set(x_169, 2, x_166);
lean_ctor_set(x_169, 3, x_66);
x_170 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_170, 0, x_73);
lean_ctor_set(x_170, 1, x_167);
lean_ctor_set(x_170, 2, x_168);
lean_ctor_set(x_170, 3, x_62);
x_171 = lean_ctor_get(x_144, 0);
lean_inc(x_171);
lean_dec(x_144);
x_172 = l_Lean_Environment_mainModule(x_171);
lean_dec(x_171);
x_173 = lean_mk_string_unchecked("congrArg", 8, 8);
lean_inc(x_173);
x_174 = l_String_toSubstring_x27(x_173);
x_175 = l_Lean_Name_mkStr1(x_173);
lean_inc(x_175);
x_176 = l_Lean_addMacroScope(x_172, x_175, x_161);
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 1, x_151);
lean_ctor_set(x_57, 0, x_175);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_57);
lean_ctor_set(x_177, 1, x_164);
x_178 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_178, 0, x_82);
lean_ctor_set(x_178, 1, x_174);
lean_ctor_set(x_178, 2, x_176);
lean_ctor_set(x_178, 3, x_177);
x_179 = lean_box(0);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_170);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_array_size(x_5);
x_183 = lean_unsigned_to_nat(0u);
x_184 = lean_usize_of_nat(x_183);
x_185 = l_Array_mapMUnsafe_map___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(x_182, x_184, x_5, x_54, x_55, x_145);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_188, 0, x_160);
lean_ctor_set(x_188, 1, x_162);
lean_ctor_set(x_188, 2, x_163);
lean_ctor_set(x_188, 3, x_71);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_169);
lean_ctor_set(x_189, 1, x_181);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_box(0);
x_192 = l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(x_190, x_191);
x_193 = l_Array_empty(lean_box(0));
x_194 = lean_array_get_size(x_186);
x_195 = lean_nat_dec_lt(x_183, x_194);
if (x_195 == 0)
{
lean_dec(x_194);
lean_dec(x_186);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_191;
x_40 = x_187;
x_41 = x_54;
x_42 = x_192;
x_43 = x_193;
goto block_51;
}
else
{
uint8_t x_196; 
x_196 = lean_nat_dec_le(x_194, x_194);
if (x_196 == 0)
{
lean_dec(x_194);
lean_dec(x_186);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_191;
x_40 = x_187;
x_41 = x_54;
x_42 = x_192;
x_43 = x_193;
goto block_51;
}
else
{
size_t x_197; lean_object* x_198; 
x_197 = lean_usize_of_nat(x_194);
lean_dec(x_194);
x_198 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__6(x_186, x_184, x_197, x_193);
lean_dec(x_186);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_191;
x_40 = x_187;
x_41 = x_54;
x_42 = x_192;
x_43 = x_198;
goto block_51;
}
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_181);
lean_dec(x_169);
lean_dec(x_71);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_160);
lean_dec(x_54);
lean_dec(x_35);
lean_dec(x_4);
lean_dec(x_3);
x_199 = lean_ctor_get(x_185, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_185, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_201 = x_185;
} else {
 lean_dec_ref(x_185);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; size_t x_246; lean_object* x_247; size_t x_248; lean_object* x_249; 
x_203 = lean_ctor_get(x_80, 0);
x_204 = lean_ctor_get(x_80, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_80);
x_205 = lean_st_ref_get(x_55, x_204);
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
x_209 = lean_ctor_get(x_54, 5);
lean_inc(x_209);
x_210 = lean_box(0);
x_211 = l_Lean_Environment_mainModule(x_61);
lean_dec(x_61);
x_212 = lean_mk_string_unchecked("rfl", 3, 3);
lean_inc(x_212);
x_213 = l_Lean_Name_mkStr1(x_212);
x_214 = lean_box(0);
lean_inc(x_213);
if (lean_is_scalar(x_208)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_208;
 lean_ctor_set_tag(x_215, 1);
}
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
x_216 = l_Lean_Environment_mainModule(x_70);
lean_dec(x_70);
x_217 = lean_mk_string_unchecked("trivial", 7, 7);
lean_inc(x_217);
x_218 = l_Lean_Name_mkStr1(x_217);
lean_inc(x_218);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_214);
x_220 = l_Lean_Environment_mainModule(x_79);
lean_dec(x_79);
x_221 = lean_mk_string_unchecked("congrFun", 8, 8);
lean_inc(x_221);
x_222 = l_Lean_Name_mkStr1(x_221);
lean_inc(x_222);
lean_ctor_set_tag(x_75, 1);
lean_ctor_set(x_75, 1, x_214);
lean_ctor_set(x_75, 0, x_222);
x_223 = lean_unbox(x_210);
x_224 = l_Lean_SourceInfo_fromRef(x_209, x_223);
lean_dec(x_209);
x_225 = lean_ctor_get(x_54, 10);
lean_inc(x_225);
x_226 = l_String_toSubstring_x27(x_212);
lean_inc(x_225);
x_227 = l_Lean_addMacroScope(x_211, x_213, x_225);
x_228 = lean_box(0);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 1, x_228);
lean_ctor_set(x_71, 0, x_215);
x_229 = l_String_toSubstring_x27(x_217);
lean_inc(x_225);
x_230 = l_Lean_addMacroScope(x_216, x_218, x_225);
lean_ctor_set_tag(x_66, 1);
lean_ctor_set(x_66, 1, x_228);
lean_ctor_set(x_66, 0, x_219);
x_231 = l_String_toSubstring_x27(x_221);
lean_inc(x_225);
x_232 = l_Lean_addMacroScope(x_220, x_222, x_225);
lean_ctor_set_tag(x_62, 1);
lean_ctor_set(x_62, 1, x_228);
lean_ctor_set(x_62, 0, x_75);
x_233 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_233, 0, x_64);
lean_ctor_set(x_233, 1, x_229);
lean_ctor_set(x_233, 2, x_230);
lean_ctor_set(x_233, 3, x_66);
x_234 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_234, 0, x_73);
lean_ctor_set(x_234, 1, x_231);
lean_ctor_set(x_234, 2, x_232);
lean_ctor_set(x_234, 3, x_62);
x_235 = lean_ctor_get(x_206, 0);
lean_inc(x_235);
lean_dec(x_206);
x_236 = l_Lean_Environment_mainModule(x_235);
lean_dec(x_235);
x_237 = lean_mk_string_unchecked("congrArg", 8, 8);
lean_inc(x_237);
x_238 = l_String_toSubstring_x27(x_237);
x_239 = l_Lean_Name_mkStr1(x_237);
lean_inc(x_239);
x_240 = l_Lean_addMacroScope(x_236, x_239, x_225);
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 1, x_214);
lean_ctor_set(x_57, 0, x_239);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_57);
lean_ctor_set(x_241, 1, x_228);
x_242 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_242, 0, x_203);
lean_ctor_set(x_242, 1, x_238);
lean_ctor_set(x_242, 2, x_240);
lean_ctor_set(x_242, 3, x_241);
x_243 = lean_box(0);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_234);
lean_ctor_set(x_245, 1, x_244);
x_246 = lean_array_size(x_5);
x_247 = lean_unsigned_to_nat(0u);
x_248 = lean_usize_of_nat(x_247);
x_249 = l_Array_mapMUnsafe_map___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(x_246, x_248, x_5, x_54, x_55, x_207);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_252, 0, x_224);
lean_ctor_set(x_252, 1, x_226);
lean_ctor_set(x_252, 2, x_227);
lean_ctor_set(x_252, 3, x_71);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_233);
lean_ctor_set(x_253, 1, x_245);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_box(0);
x_256 = l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(x_254, x_255);
x_257 = l_Array_empty(lean_box(0));
x_258 = lean_array_get_size(x_250);
x_259 = lean_nat_dec_lt(x_247, x_258);
if (x_259 == 0)
{
lean_dec(x_258);
lean_dec(x_250);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_255;
x_40 = x_251;
x_41 = x_54;
x_42 = x_256;
x_43 = x_257;
goto block_51;
}
else
{
uint8_t x_260; 
x_260 = lean_nat_dec_le(x_258, x_258);
if (x_260 == 0)
{
lean_dec(x_258);
lean_dec(x_250);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_255;
x_40 = x_251;
x_41 = x_54;
x_42 = x_256;
x_43 = x_257;
goto block_51;
}
else
{
size_t x_261; lean_object* x_262; 
x_261 = lean_usize_of_nat(x_258);
lean_dec(x_258);
x_262 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__6(x_250, x_248, x_261, x_257);
lean_dec(x_250);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_255;
x_40 = x_251;
x_41 = x_54;
x_42 = x_256;
x_43 = x_262;
goto block_51;
}
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_245);
lean_dec(x_233);
lean_dec(x_71);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_224);
lean_dec(x_54);
lean_dec(x_35);
lean_dec(x_4);
lean_dec(x_3);
x_263 = lean_ctor_get(x_249, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_249, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_265 = x_249;
} else {
 lean_dec_ref(x_249);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; size_t x_316; lean_object* x_317; size_t x_318; lean_object* x_319; 
x_267 = lean_ctor_get(x_75, 0);
x_268 = lean_ctor_get(x_75, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_75);
x_269 = lean_ctor_get(x_267, 0);
lean_inc(x_269);
lean_dec(x_267);
x_270 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(x_52, x_53, x_54, x_55, x_268);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_273 = x_270;
} else {
 lean_dec_ref(x_270);
 x_273 = lean_box(0);
}
x_274 = lean_st_ref_get(x_55, x_272);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_277 = x_274;
} else {
 lean_dec_ref(x_274);
 x_277 = lean_box(0);
}
x_278 = lean_ctor_get(x_54, 5);
lean_inc(x_278);
x_279 = lean_box(0);
x_280 = l_Lean_Environment_mainModule(x_61);
lean_dec(x_61);
x_281 = lean_mk_string_unchecked("rfl", 3, 3);
lean_inc(x_281);
x_282 = l_Lean_Name_mkStr1(x_281);
x_283 = lean_box(0);
lean_inc(x_282);
if (lean_is_scalar(x_277)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_277;
 lean_ctor_set_tag(x_284, 1);
}
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
x_285 = l_Lean_Environment_mainModule(x_70);
lean_dec(x_70);
x_286 = lean_mk_string_unchecked("trivial", 7, 7);
lean_inc(x_286);
x_287 = l_Lean_Name_mkStr1(x_286);
lean_inc(x_287);
if (lean_is_scalar(x_273)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_273;
 lean_ctor_set_tag(x_288, 1);
}
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_283);
x_289 = l_Lean_Environment_mainModule(x_269);
lean_dec(x_269);
x_290 = lean_mk_string_unchecked("congrFun", 8, 8);
lean_inc(x_290);
x_291 = l_Lean_Name_mkStr1(x_290);
lean_inc(x_291);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_283);
x_293 = lean_unbox(x_279);
x_294 = l_Lean_SourceInfo_fromRef(x_278, x_293);
lean_dec(x_278);
x_295 = lean_ctor_get(x_54, 10);
lean_inc(x_295);
x_296 = l_String_toSubstring_x27(x_281);
lean_inc(x_295);
x_297 = l_Lean_addMacroScope(x_280, x_282, x_295);
x_298 = lean_box(0);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 1, x_298);
lean_ctor_set(x_71, 0, x_284);
x_299 = l_String_toSubstring_x27(x_286);
lean_inc(x_295);
x_300 = l_Lean_addMacroScope(x_285, x_287, x_295);
lean_ctor_set_tag(x_66, 1);
lean_ctor_set(x_66, 1, x_298);
lean_ctor_set(x_66, 0, x_288);
x_301 = l_String_toSubstring_x27(x_290);
lean_inc(x_295);
x_302 = l_Lean_addMacroScope(x_289, x_291, x_295);
lean_ctor_set_tag(x_62, 1);
lean_ctor_set(x_62, 1, x_298);
lean_ctor_set(x_62, 0, x_292);
x_303 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_303, 0, x_64);
lean_ctor_set(x_303, 1, x_299);
lean_ctor_set(x_303, 2, x_300);
lean_ctor_set(x_303, 3, x_66);
x_304 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_304, 0, x_73);
lean_ctor_set(x_304, 1, x_301);
lean_ctor_set(x_304, 2, x_302);
lean_ctor_set(x_304, 3, x_62);
x_305 = lean_ctor_get(x_275, 0);
lean_inc(x_305);
lean_dec(x_275);
x_306 = l_Lean_Environment_mainModule(x_305);
lean_dec(x_305);
x_307 = lean_mk_string_unchecked("congrArg", 8, 8);
lean_inc(x_307);
x_308 = l_String_toSubstring_x27(x_307);
x_309 = l_Lean_Name_mkStr1(x_307);
lean_inc(x_309);
x_310 = l_Lean_addMacroScope(x_306, x_309, x_295);
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 1, x_283);
lean_ctor_set(x_57, 0, x_309);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_57);
lean_ctor_set(x_311, 1, x_298);
x_312 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_312, 0, x_271);
lean_ctor_set(x_312, 1, x_308);
lean_ctor_set(x_312, 2, x_310);
lean_ctor_set(x_312, 3, x_311);
x_313 = lean_box(0);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_304);
lean_ctor_set(x_315, 1, x_314);
x_316 = lean_array_size(x_5);
x_317 = lean_unsigned_to_nat(0u);
x_318 = lean_usize_of_nat(x_317);
x_319 = l_Array_mapMUnsafe_map___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(x_316, x_318, x_5, x_54, x_55, x_276);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; 
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
lean_dec(x_319);
x_322 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_322, 0, x_294);
lean_ctor_set(x_322, 1, x_296);
lean_ctor_set(x_322, 2, x_297);
lean_ctor_set(x_322, 3, x_71);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_303);
lean_ctor_set(x_323, 1, x_315);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
x_325 = lean_box(0);
x_326 = l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(x_324, x_325);
x_327 = l_Array_empty(lean_box(0));
x_328 = lean_array_get_size(x_320);
x_329 = lean_nat_dec_lt(x_317, x_328);
if (x_329 == 0)
{
lean_dec(x_328);
lean_dec(x_320);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_325;
x_40 = x_321;
x_41 = x_54;
x_42 = x_326;
x_43 = x_327;
goto block_51;
}
else
{
uint8_t x_330; 
x_330 = lean_nat_dec_le(x_328, x_328);
if (x_330 == 0)
{
lean_dec(x_328);
lean_dec(x_320);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_325;
x_40 = x_321;
x_41 = x_54;
x_42 = x_326;
x_43 = x_327;
goto block_51;
}
else
{
size_t x_331; lean_object* x_332; 
x_331 = lean_usize_of_nat(x_328);
lean_dec(x_328);
x_332 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__6(x_320, x_318, x_331, x_327);
lean_dec(x_320);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_325;
x_40 = x_321;
x_41 = x_54;
x_42 = x_326;
x_43 = x_332;
goto block_51;
}
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_315);
lean_dec(x_303);
lean_dec(x_71);
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_294);
lean_dec(x_54);
lean_dec(x_35);
lean_dec(x_4);
lean_dec(x_3);
x_333 = lean_ctor_get(x_319, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_319, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_335 = x_319;
} else {
 lean_dec_ref(x_319);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(1, 2, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_333);
lean_ctor_set(x_336, 1, x_334);
return x_336;
}
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; size_t x_391; lean_object* x_392; size_t x_393; lean_object* x_394; 
x_337 = lean_ctor_get(x_71, 0);
x_338 = lean_ctor_get(x_71, 1);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_71);
x_339 = lean_st_ref_get(x_55, x_338);
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 x_342 = x_339;
} else {
 lean_dec_ref(x_339);
 x_342 = lean_box(0);
}
x_343 = lean_ctor_get(x_340, 0);
lean_inc(x_343);
lean_dec(x_340);
x_344 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(x_52, x_53, x_54, x_55, x_341);
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_347 = x_344;
} else {
 lean_dec_ref(x_344);
 x_347 = lean_box(0);
}
x_348 = lean_st_ref_get(x_55, x_346);
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_351 = x_348;
} else {
 lean_dec_ref(x_348);
 x_351 = lean_box(0);
}
x_352 = lean_ctor_get(x_54, 5);
lean_inc(x_352);
x_353 = lean_box(0);
x_354 = l_Lean_Environment_mainModule(x_61);
lean_dec(x_61);
x_355 = lean_mk_string_unchecked("rfl", 3, 3);
lean_inc(x_355);
x_356 = l_Lean_Name_mkStr1(x_355);
x_357 = lean_box(0);
lean_inc(x_356);
if (lean_is_scalar(x_351)) {
 x_358 = lean_alloc_ctor(1, 2, 0);
} else {
 x_358 = x_351;
 lean_ctor_set_tag(x_358, 1);
}
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_357);
x_359 = l_Lean_Environment_mainModule(x_70);
lean_dec(x_70);
x_360 = lean_mk_string_unchecked("trivial", 7, 7);
lean_inc(x_360);
x_361 = l_Lean_Name_mkStr1(x_360);
lean_inc(x_361);
if (lean_is_scalar(x_347)) {
 x_362 = lean_alloc_ctor(1, 2, 0);
} else {
 x_362 = x_347;
 lean_ctor_set_tag(x_362, 1);
}
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_357);
x_363 = l_Lean_Environment_mainModule(x_343);
lean_dec(x_343);
x_364 = lean_mk_string_unchecked("congrFun", 8, 8);
lean_inc(x_364);
x_365 = l_Lean_Name_mkStr1(x_364);
lean_inc(x_365);
if (lean_is_scalar(x_342)) {
 x_366 = lean_alloc_ctor(1, 2, 0);
} else {
 x_366 = x_342;
 lean_ctor_set_tag(x_366, 1);
}
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_357);
x_367 = lean_unbox(x_353);
x_368 = l_Lean_SourceInfo_fromRef(x_352, x_367);
lean_dec(x_352);
x_369 = lean_ctor_get(x_54, 10);
lean_inc(x_369);
x_370 = l_String_toSubstring_x27(x_355);
lean_inc(x_369);
x_371 = l_Lean_addMacroScope(x_354, x_356, x_369);
x_372 = lean_box(0);
x_373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_373, 0, x_358);
lean_ctor_set(x_373, 1, x_372);
x_374 = l_String_toSubstring_x27(x_360);
lean_inc(x_369);
x_375 = l_Lean_addMacroScope(x_359, x_361, x_369);
lean_ctor_set_tag(x_66, 1);
lean_ctor_set(x_66, 1, x_372);
lean_ctor_set(x_66, 0, x_362);
x_376 = l_String_toSubstring_x27(x_364);
lean_inc(x_369);
x_377 = l_Lean_addMacroScope(x_363, x_365, x_369);
lean_ctor_set_tag(x_62, 1);
lean_ctor_set(x_62, 1, x_372);
lean_ctor_set(x_62, 0, x_366);
x_378 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_378, 0, x_64);
lean_ctor_set(x_378, 1, x_374);
lean_ctor_set(x_378, 2, x_375);
lean_ctor_set(x_378, 3, x_66);
x_379 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_379, 0, x_337);
lean_ctor_set(x_379, 1, x_376);
lean_ctor_set(x_379, 2, x_377);
lean_ctor_set(x_379, 3, x_62);
x_380 = lean_ctor_get(x_349, 0);
lean_inc(x_380);
lean_dec(x_349);
x_381 = l_Lean_Environment_mainModule(x_380);
lean_dec(x_380);
x_382 = lean_mk_string_unchecked("congrArg", 8, 8);
lean_inc(x_382);
x_383 = l_String_toSubstring_x27(x_382);
x_384 = l_Lean_Name_mkStr1(x_382);
lean_inc(x_384);
x_385 = l_Lean_addMacroScope(x_381, x_384, x_369);
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 1, x_357);
lean_ctor_set(x_57, 0, x_384);
x_386 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_386, 0, x_57);
lean_ctor_set(x_386, 1, x_372);
x_387 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_387, 0, x_345);
lean_ctor_set(x_387, 1, x_383);
lean_ctor_set(x_387, 2, x_385);
lean_ctor_set(x_387, 3, x_386);
x_388 = lean_box(0);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
x_390 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_390, 0, x_379);
lean_ctor_set(x_390, 1, x_389);
x_391 = lean_array_size(x_5);
x_392 = lean_unsigned_to_nat(0u);
x_393 = lean_usize_of_nat(x_392);
x_394 = l_Array_mapMUnsafe_map___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(x_391, x_393, x_5, x_54, x_55, x_350);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
lean_dec(x_394);
x_397 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_397, 0, x_368);
lean_ctor_set(x_397, 1, x_370);
lean_ctor_set(x_397, 2, x_371);
lean_ctor_set(x_397, 3, x_373);
x_398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_398, 0, x_378);
lean_ctor_set(x_398, 1, x_390);
x_399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set(x_399, 1, x_398);
x_400 = lean_box(0);
x_401 = l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(x_399, x_400);
x_402 = l_Array_empty(lean_box(0));
x_403 = lean_array_get_size(x_395);
x_404 = lean_nat_dec_lt(x_392, x_403);
if (x_404 == 0)
{
lean_dec(x_403);
lean_dec(x_395);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_400;
x_40 = x_396;
x_41 = x_54;
x_42 = x_401;
x_43 = x_402;
goto block_51;
}
else
{
uint8_t x_405; 
x_405 = lean_nat_dec_le(x_403, x_403);
if (x_405 == 0)
{
lean_dec(x_403);
lean_dec(x_395);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_400;
x_40 = x_396;
x_41 = x_54;
x_42 = x_401;
x_43 = x_402;
goto block_51;
}
else
{
size_t x_406; lean_object* x_407; 
x_406 = lean_usize_of_nat(x_403);
lean_dec(x_403);
x_407 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__6(x_395, x_393, x_406, x_402);
lean_dec(x_395);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_400;
x_40 = x_396;
x_41 = x_54;
x_42 = x_401;
x_43 = x_407;
goto block_51;
}
}
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_390);
lean_dec(x_378);
lean_dec(x_373);
lean_dec(x_371);
lean_dec(x_370);
lean_dec(x_368);
lean_dec(x_54);
lean_dec(x_35);
lean_dec(x_4);
lean_dec(x_3);
x_408 = lean_ctor_get(x_394, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_394, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_410 = x_394;
} else {
 lean_dec_ref(x_394);
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
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; size_t x_472; lean_object* x_473; size_t x_474; lean_object* x_475; 
x_412 = lean_ctor_get(x_66, 0);
x_413 = lean_ctor_get(x_66, 1);
lean_inc(x_413);
lean_inc(x_412);
lean_dec(x_66);
x_414 = lean_ctor_get(x_412, 0);
lean_inc(x_414);
lean_dec(x_412);
x_415 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(x_52, x_53, x_54, x_55, x_413);
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_415, 1);
lean_inc(x_417);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_418 = x_415;
} else {
 lean_dec_ref(x_415);
 x_418 = lean_box(0);
}
x_419 = lean_st_ref_get(x_55, x_417);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 x_422 = x_419;
} else {
 lean_dec_ref(x_419);
 x_422 = lean_box(0);
}
x_423 = lean_ctor_get(x_420, 0);
lean_inc(x_423);
lean_dec(x_420);
x_424 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(x_52, x_53, x_54, x_55, x_421);
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_424, 1);
lean_inc(x_426);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 x_427 = x_424;
} else {
 lean_dec_ref(x_424);
 x_427 = lean_box(0);
}
x_428 = lean_st_ref_get(x_55, x_426);
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_431 = x_428;
} else {
 lean_dec_ref(x_428);
 x_431 = lean_box(0);
}
x_432 = lean_ctor_get(x_54, 5);
lean_inc(x_432);
x_433 = lean_box(0);
x_434 = l_Lean_Environment_mainModule(x_61);
lean_dec(x_61);
x_435 = lean_mk_string_unchecked("rfl", 3, 3);
lean_inc(x_435);
x_436 = l_Lean_Name_mkStr1(x_435);
x_437 = lean_box(0);
lean_inc(x_436);
if (lean_is_scalar(x_431)) {
 x_438 = lean_alloc_ctor(1, 2, 0);
} else {
 x_438 = x_431;
 lean_ctor_set_tag(x_438, 1);
}
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set(x_438, 1, x_437);
x_439 = l_Lean_Environment_mainModule(x_414);
lean_dec(x_414);
x_440 = lean_mk_string_unchecked("trivial", 7, 7);
lean_inc(x_440);
x_441 = l_Lean_Name_mkStr1(x_440);
lean_inc(x_441);
if (lean_is_scalar(x_427)) {
 x_442 = lean_alloc_ctor(1, 2, 0);
} else {
 x_442 = x_427;
 lean_ctor_set_tag(x_442, 1);
}
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_437);
x_443 = l_Lean_Environment_mainModule(x_423);
lean_dec(x_423);
x_444 = lean_mk_string_unchecked("congrFun", 8, 8);
lean_inc(x_444);
x_445 = l_Lean_Name_mkStr1(x_444);
lean_inc(x_445);
if (lean_is_scalar(x_422)) {
 x_446 = lean_alloc_ctor(1, 2, 0);
} else {
 x_446 = x_422;
 lean_ctor_set_tag(x_446, 1);
}
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_437);
x_447 = lean_unbox(x_433);
x_448 = l_Lean_SourceInfo_fromRef(x_432, x_447);
lean_dec(x_432);
x_449 = lean_ctor_get(x_54, 10);
lean_inc(x_449);
x_450 = l_String_toSubstring_x27(x_435);
lean_inc(x_449);
x_451 = l_Lean_addMacroScope(x_434, x_436, x_449);
x_452 = lean_box(0);
if (lean_is_scalar(x_418)) {
 x_453 = lean_alloc_ctor(1, 2, 0);
} else {
 x_453 = x_418;
 lean_ctor_set_tag(x_453, 1);
}
lean_ctor_set(x_453, 0, x_438);
lean_ctor_set(x_453, 1, x_452);
x_454 = l_String_toSubstring_x27(x_440);
lean_inc(x_449);
x_455 = l_Lean_addMacroScope(x_439, x_441, x_449);
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_442);
lean_ctor_set(x_456, 1, x_452);
x_457 = l_String_toSubstring_x27(x_444);
lean_inc(x_449);
x_458 = l_Lean_addMacroScope(x_443, x_445, x_449);
lean_ctor_set_tag(x_62, 1);
lean_ctor_set(x_62, 1, x_452);
lean_ctor_set(x_62, 0, x_446);
x_459 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_459, 0, x_64);
lean_ctor_set(x_459, 1, x_454);
lean_ctor_set(x_459, 2, x_455);
lean_ctor_set(x_459, 3, x_456);
x_460 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_460, 0, x_416);
lean_ctor_set(x_460, 1, x_457);
lean_ctor_set(x_460, 2, x_458);
lean_ctor_set(x_460, 3, x_62);
x_461 = lean_ctor_get(x_429, 0);
lean_inc(x_461);
lean_dec(x_429);
x_462 = l_Lean_Environment_mainModule(x_461);
lean_dec(x_461);
x_463 = lean_mk_string_unchecked("congrArg", 8, 8);
lean_inc(x_463);
x_464 = l_String_toSubstring_x27(x_463);
x_465 = l_Lean_Name_mkStr1(x_463);
lean_inc(x_465);
x_466 = l_Lean_addMacroScope(x_462, x_465, x_449);
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 1, x_437);
lean_ctor_set(x_57, 0, x_465);
x_467 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_467, 0, x_57);
lean_ctor_set(x_467, 1, x_452);
x_468 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_468, 0, x_425);
lean_ctor_set(x_468, 1, x_464);
lean_ctor_set(x_468, 2, x_466);
lean_ctor_set(x_468, 3, x_467);
x_469 = lean_box(0);
x_470 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_470, 0, x_468);
lean_ctor_set(x_470, 1, x_469);
x_471 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_471, 0, x_460);
lean_ctor_set(x_471, 1, x_470);
x_472 = lean_array_size(x_5);
x_473 = lean_unsigned_to_nat(0u);
x_474 = lean_usize_of_nat(x_473);
x_475 = l_Array_mapMUnsafe_map___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(x_472, x_474, x_5, x_54, x_55, x_430);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; 
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_475, 1);
lean_inc(x_477);
lean_dec(x_475);
x_478 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_478, 0, x_448);
lean_ctor_set(x_478, 1, x_450);
lean_ctor_set(x_478, 2, x_451);
lean_ctor_set(x_478, 3, x_453);
x_479 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_479, 0, x_459);
lean_ctor_set(x_479, 1, x_471);
x_480 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_480, 0, x_478);
lean_ctor_set(x_480, 1, x_479);
x_481 = lean_box(0);
x_482 = l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(x_480, x_481);
x_483 = l_Array_empty(lean_box(0));
x_484 = lean_array_get_size(x_476);
x_485 = lean_nat_dec_lt(x_473, x_484);
if (x_485 == 0)
{
lean_dec(x_484);
lean_dec(x_476);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_481;
x_40 = x_477;
x_41 = x_54;
x_42 = x_482;
x_43 = x_483;
goto block_51;
}
else
{
uint8_t x_486; 
x_486 = lean_nat_dec_le(x_484, x_484);
if (x_486 == 0)
{
lean_dec(x_484);
lean_dec(x_476);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_481;
x_40 = x_477;
x_41 = x_54;
x_42 = x_482;
x_43 = x_483;
goto block_51;
}
else
{
size_t x_487; lean_object* x_488; 
x_487 = lean_usize_of_nat(x_484);
lean_dec(x_484);
x_488 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__6(x_476, x_474, x_487, x_483);
lean_dec(x_476);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_481;
x_40 = x_477;
x_41 = x_54;
x_42 = x_482;
x_43 = x_488;
goto block_51;
}
}
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_471);
lean_dec(x_459);
lean_dec(x_453);
lean_dec(x_451);
lean_dec(x_450);
lean_dec(x_448);
lean_dec(x_54);
lean_dec(x_35);
lean_dec(x_4);
lean_dec(x_3);
x_489 = lean_ctor_get(x_475, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_475, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 x_491 = x_475;
} else {
 lean_dec_ref(x_475);
 x_491 = lean_box(0);
}
if (lean_is_scalar(x_491)) {
 x_492 = lean_alloc_ctor(1, 2, 0);
} else {
 x_492 = x_491;
}
lean_ctor_set(x_492, 0, x_489);
lean_ctor_set(x_492, 1, x_490);
return x_492;
}
}
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; uint8_t x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; size_t x_558; lean_object* x_559; size_t x_560; lean_object* x_561; 
x_493 = lean_ctor_get(x_62, 0);
x_494 = lean_ctor_get(x_62, 1);
lean_inc(x_494);
lean_inc(x_493);
lean_dec(x_62);
x_495 = lean_st_ref_get(x_55, x_494);
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_495, 1);
lean_inc(x_497);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_498 = x_495;
} else {
 lean_dec_ref(x_495);
 x_498 = lean_box(0);
}
x_499 = lean_ctor_get(x_496, 0);
lean_inc(x_499);
lean_dec(x_496);
x_500 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(x_52, x_53, x_54, x_55, x_497);
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 x_503 = x_500;
} else {
 lean_dec_ref(x_500);
 x_503 = lean_box(0);
}
x_504 = lean_st_ref_get(x_55, x_502);
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_504, 1);
lean_inc(x_506);
if (lean_is_exclusive(x_504)) {
 lean_ctor_release(x_504, 0);
 lean_ctor_release(x_504, 1);
 x_507 = x_504;
} else {
 lean_dec_ref(x_504);
 x_507 = lean_box(0);
}
x_508 = lean_ctor_get(x_505, 0);
lean_inc(x_508);
lean_dec(x_505);
x_509 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(x_52, x_53, x_54, x_55, x_506);
x_510 = lean_ctor_get(x_509, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_509, 1);
lean_inc(x_511);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 x_512 = x_509;
} else {
 lean_dec_ref(x_509);
 x_512 = lean_box(0);
}
x_513 = lean_st_ref_get(x_55, x_511);
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 lean_ctor_release(x_513, 1);
 x_516 = x_513;
} else {
 lean_dec_ref(x_513);
 x_516 = lean_box(0);
}
x_517 = lean_ctor_get(x_54, 5);
lean_inc(x_517);
x_518 = lean_box(0);
x_519 = l_Lean_Environment_mainModule(x_61);
lean_dec(x_61);
x_520 = lean_mk_string_unchecked("rfl", 3, 3);
lean_inc(x_520);
x_521 = l_Lean_Name_mkStr1(x_520);
x_522 = lean_box(0);
lean_inc(x_521);
if (lean_is_scalar(x_516)) {
 x_523 = lean_alloc_ctor(1, 2, 0);
} else {
 x_523 = x_516;
 lean_ctor_set_tag(x_523, 1);
}
lean_ctor_set(x_523, 0, x_521);
lean_ctor_set(x_523, 1, x_522);
x_524 = l_Lean_Environment_mainModule(x_499);
lean_dec(x_499);
x_525 = lean_mk_string_unchecked("trivial", 7, 7);
lean_inc(x_525);
x_526 = l_Lean_Name_mkStr1(x_525);
lean_inc(x_526);
if (lean_is_scalar(x_512)) {
 x_527 = lean_alloc_ctor(1, 2, 0);
} else {
 x_527 = x_512;
 lean_ctor_set_tag(x_527, 1);
}
lean_ctor_set(x_527, 0, x_526);
lean_ctor_set(x_527, 1, x_522);
x_528 = l_Lean_Environment_mainModule(x_508);
lean_dec(x_508);
x_529 = lean_mk_string_unchecked("congrFun", 8, 8);
lean_inc(x_529);
x_530 = l_Lean_Name_mkStr1(x_529);
lean_inc(x_530);
if (lean_is_scalar(x_507)) {
 x_531 = lean_alloc_ctor(1, 2, 0);
} else {
 x_531 = x_507;
 lean_ctor_set_tag(x_531, 1);
}
lean_ctor_set(x_531, 0, x_530);
lean_ctor_set(x_531, 1, x_522);
x_532 = lean_unbox(x_518);
x_533 = l_Lean_SourceInfo_fromRef(x_517, x_532);
lean_dec(x_517);
x_534 = lean_ctor_get(x_54, 10);
lean_inc(x_534);
x_535 = l_String_toSubstring_x27(x_520);
lean_inc(x_534);
x_536 = l_Lean_addMacroScope(x_519, x_521, x_534);
x_537 = lean_box(0);
if (lean_is_scalar(x_503)) {
 x_538 = lean_alloc_ctor(1, 2, 0);
} else {
 x_538 = x_503;
 lean_ctor_set_tag(x_538, 1);
}
lean_ctor_set(x_538, 0, x_523);
lean_ctor_set(x_538, 1, x_537);
x_539 = l_String_toSubstring_x27(x_525);
lean_inc(x_534);
x_540 = l_Lean_addMacroScope(x_524, x_526, x_534);
if (lean_is_scalar(x_498)) {
 x_541 = lean_alloc_ctor(1, 2, 0);
} else {
 x_541 = x_498;
 lean_ctor_set_tag(x_541, 1);
}
lean_ctor_set(x_541, 0, x_527);
lean_ctor_set(x_541, 1, x_537);
x_542 = l_String_toSubstring_x27(x_529);
lean_inc(x_534);
x_543 = l_Lean_addMacroScope(x_528, x_530, x_534);
x_544 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_544, 0, x_531);
lean_ctor_set(x_544, 1, x_537);
x_545 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_545, 0, x_493);
lean_ctor_set(x_545, 1, x_539);
lean_ctor_set(x_545, 2, x_540);
lean_ctor_set(x_545, 3, x_541);
x_546 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_546, 0, x_501);
lean_ctor_set(x_546, 1, x_542);
lean_ctor_set(x_546, 2, x_543);
lean_ctor_set(x_546, 3, x_544);
x_547 = lean_ctor_get(x_514, 0);
lean_inc(x_547);
lean_dec(x_514);
x_548 = l_Lean_Environment_mainModule(x_547);
lean_dec(x_547);
x_549 = lean_mk_string_unchecked("congrArg", 8, 8);
lean_inc(x_549);
x_550 = l_String_toSubstring_x27(x_549);
x_551 = l_Lean_Name_mkStr1(x_549);
lean_inc(x_551);
x_552 = l_Lean_addMacroScope(x_548, x_551, x_534);
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 1, x_522);
lean_ctor_set(x_57, 0, x_551);
x_553 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_553, 0, x_57);
lean_ctor_set(x_553, 1, x_537);
x_554 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_554, 0, x_510);
lean_ctor_set(x_554, 1, x_550);
lean_ctor_set(x_554, 2, x_552);
lean_ctor_set(x_554, 3, x_553);
x_555 = lean_box(0);
x_556 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_556, 0, x_554);
lean_ctor_set(x_556, 1, x_555);
x_557 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_557, 0, x_546);
lean_ctor_set(x_557, 1, x_556);
x_558 = lean_array_size(x_5);
x_559 = lean_unsigned_to_nat(0u);
x_560 = lean_usize_of_nat(x_559);
x_561 = l_Array_mapMUnsafe_map___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(x_558, x_560, x_5, x_54, x_55, x_515);
if (lean_obj_tag(x_561) == 0)
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; uint8_t x_571; 
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_561, 1);
lean_inc(x_563);
lean_dec(x_561);
x_564 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_564, 0, x_533);
lean_ctor_set(x_564, 1, x_535);
lean_ctor_set(x_564, 2, x_536);
lean_ctor_set(x_564, 3, x_538);
x_565 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_565, 0, x_545);
lean_ctor_set(x_565, 1, x_557);
x_566 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_566, 0, x_564);
lean_ctor_set(x_566, 1, x_565);
x_567 = lean_box(0);
x_568 = l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(x_566, x_567);
x_569 = l_Array_empty(lean_box(0));
x_570 = lean_array_get_size(x_562);
x_571 = lean_nat_dec_lt(x_559, x_570);
if (x_571 == 0)
{
lean_dec(x_570);
lean_dec(x_562);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_567;
x_40 = x_563;
x_41 = x_54;
x_42 = x_568;
x_43 = x_569;
goto block_51;
}
else
{
uint8_t x_572; 
x_572 = lean_nat_dec_le(x_570, x_570);
if (x_572 == 0)
{
lean_dec(x_570);
lean_dec(x_562);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_567;
x_40 = x_563;
x_41 = x_54;
x_42 = x_568;
x_43 = x_569;
goto block_51;
}
else
{
size_t x_573; lean_object* x_574; 
x_573 = lean_usize_of_nat(x_570);
lean_dec(x_570);
x_574 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__6(x_562, x_560, x_573, x_569);
lean_dec(x_562);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_567;
x_40 = x_563;
x_41 = x_54;
x_42 = x_568;
x_43 = x_574;
goto block_51;
}
}
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
lean_dec(x_557);
lean_dec(x_545);
lean_dec(x_538);
lean_dec(x_536);
lean_dec(x_535);
lean_dec(x_533);
lean_dec(x_54);
lean_dec(x_35);
lean_dec(x_4);
lean_dec(x_3);
x_575 = lean_ctor_get(x_561, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_561, 1);
lean_inc(x_576);
if (lean_is_exclusive(x_561)) {
 lean_ctor_release(x_561, 0);
 lean_ctor_release(x_561, 1);
 x_577 = x_561;
} else {
 lean_dec_ref(x_561);
 x_577 = lean_box(0);
}
if (lean_is_scalar(x_577)) {
 x_578 = lean_alloc_ctor(1, 2, 0);
} else {
 x_578 = x_577;
}
lean_ctor_set(x_578, 0, x_575);
lean_ctor_set(x_578, 1, x_576);
return x_578;
}
}
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; uint8_t x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; size_t x_650; lean_object* x_651; size_t x_652; lean_object* x_653; 
x_579 = lean_ctor_get(x_57, 0);
x_580 = lean_ctor_get(x_57, 1);
lean_inc(x_580);
lean_inc(x_579);
lean_dec(x_57);
x_581 = lean_ctor_get(x_579, 0);
lean_inc(x_581);
lean_dec(x_579);
x_582 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(x_52, x_53, x_54, x_55, x_580);
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_582, 1);
lean_inc(x_584);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 lean_ctor_release(x_582, 1);
 x_585 = x_582;
} else {
 lean_dec_ref(x_582);
 x_585 = lean_box(0);
}
x_586 = lean_st_ref_get(x_55, x_584);
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_586, 1);
lean_inc(x_588);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 x_589 = x_586;
} else {
 lean_dec_ref(x_586);
 x_589 = lean_box(0);
}
x_590 = lean_ctor_get(x_587, 0);
lean_inc(x_590);
lean_dec(x_587);
x_591 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(x_52, x_53, x_54, x_55, x_588);
x_592 = lean_ctor_get(x_591, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_591, 1);
lean_inc(x_593);
if (lean_is_exclusive(x_591)) {
 lean_ctor_release(x_591, 0);
 lean_ctor_release(x_591, 1);
 x_594 = x_591;
} else {
 lean_dec_ref(x_591);
 x_594 = lean_box(0);
}
x_595 = lean_st_ref_get(x_55, x_593);
x_596 = lean_ctor_get(x_595, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_595, 1);
lean_inc(x_597);
if (lean_is_exclusive(x_595)) {
 lean_ctor_release(x_595, 0);
 lean_ctor_release(x_595, 1);
 x_598 = x_595;
} else {
 lean_dec_ref(x_595);
 x_598 = lean_box(0);
}
x_599 = lean_ctor_get(x_596, 0);
lean_inc(x_599);
lean_dec(x_596);
x_600 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(x_52, x_53, x_54, x_55, x_597);
x_601 = lean_ctor_get(x_600, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_600, 1);
lean_inc(x_602);
if (lean_is_exclusive(x_600)) {
 lean_ctor_release(x_600, 0);
 lean_ctor_release(x_600, 1);
 x_603 = x_600;
} else {
 lean_dec_ref(x_600);
 x_603 = lean_box(0);
}
x_604 = lean_st_ref_get(x_55, x_602);
x_605 = lean_ctor_get(x_604, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_604, 1);
lean_inc(x_606);
if (lean_is_exclusive(x_604)) {
 lean_ctor_release(x_604, 0);
 lean_ctor_release(x_604, 1);
 x_607 = x_604;
} else {
 lean_dec_ref(x_604);
 x_607 = lean_box(0);
}
x_608 = lean_ctor_get(x_54, 5);
lean_inc(x_608);
x_609 = lean_box(0);
x_610 = l_Lean_Environment_mainModule(x_581);
lean_dec(x_581);
x_611 = lean_mk_string_unchecked("rfl", 3, 3);
lean_inc(x_611);
x_612 = l_Lean_Name_mkStr1(x_611);
x_613 = lean_box(0);
lean_inc(x_612);
if (lean_is_scalar(x_607)) {
 x_614 = lean_alloc_ctor(1, 2, 0);
} else {
 x_614 = x_607;
 lean_ctor_set_tag(x_614, 1);
}
lean_ctor_set(x_614, 0, x_612);
lean_ctor_set(x_614, 1, x_613);
x_615 = l_Lean_Environment_mainModule(x_590);
lean_dec(x_590);
x_616 = lean_mk_string_unchecked("trivial", 7, 7);
lean_inc(x_616);
x_617 = l_Lean_Name_mkStr1(x_616);
lean_inc(x_617);
if (lean_is_scalar(x_603)) {
 x_618 = lean_alloc_ctor(1, 2, 0);
} else {
 x_618 = x_603;
 lean_ctor_set_tag(x_618, 1);
}
lean_ctor_set(x_618, 0, x_617);
lean_ctor_set(x_618, 1, x_613);
x_619 = l_Lean_Environment_mainModule(x_599);
lean_dec(x_599);
x_620 = lean_mk_string_unchecked("congrFun", 8, 8);
lean_inc(x_620);
x_621 = l_Lean_Name_mkStr1(x_620);
lean_inc(x_621);
if (lean_is_scalar(x_598)) {
 x_622 = lean_alloc_ctor(1, 2, 0);
} else {
 x_622 = x_598;
 lean_ctor_set_tag(x_622, 1);
}
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_613);
x_623 = lean_unbox(x_609);
x_624 = l_Lean_SourceInfo_fromRef(x_608, x_623);
lean_dec(x_608);
x_625 = lean_ctor_get(x_54, 10);
lean_inc(x_625);
x_626 = l_String_toSubstring_x27(x_611);
lean_inc(x_625);
x_627 = l_Lean_addMacroScope(x_610, x_612, x_625);
x_628 = lean_box(0);
if (lean_is_scalar(x_594)) {
 x_629 = lean_alloc_ctor(1, 2, 0);
} else {
 x_629 = x_594;
 lean_ctor_set_tag(x_629, 1);
}
lean_ctor_set(x_629, 0, x_614);
lean_ctor_set(x_629, 1, x_628);
x_630 = l_String_toSubstring_x27(x_616);
lean_inc(x_625);
x_631 = l_Lean_addMacroScope(x_615, x_617, x_625);
if (lean_is_scalar(x_589)) {
 x_632 = lean_alloc_ctor(1, 2, 0);
} else {
 x_632 = x_589;
 lean_ctor_set_tag(x_632, 1);
}
lean_ctor_set(x_632, 0, x_618);
lean_ctor_set(x_632, 1, x_628);
x_633 = l_String_toSubstring_x27(x_620);
lean_inc(x_625);
x_634 = l_Lean_addMacroScope(x_619, x_621, x_625);
if (lean_is_scalar(x_585)) {
 x_635 = lean_alloc_ctor(1, 2, 0);
} else {
 x_635 = x_585;
 lean_ctor_set_tag(x_635, 1);
}
lean_ctor_set(x_635, 0, x_622);
lean_ctor_set(x_635, 1, x_628);
x_636 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_636, 0, x_583);
lean_ctor_set(x_636, 1, x_630);
lean_ctor_set(x_636, 2, x_631);
lean_ctor_set(x_636, 3, x_632);
x_637 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_637, 0, x_592);
lean_ctor_set(x_637, 1, x_633);
lean_ctor_set(x_637, 2, x_634);
lean_ctor_set(x_637, 3, x_635);
x_638 = lean_ctor_get(x_605, 0);
lean_inc(x_638);
lean_dec(x_605);
x_639 = l_Lean_Environment_mainModule(x_638);
lean_dec(x_638);
x_640 = lean_mk_string_unchecked("congrArg", 8, 8);
lean_inc(x_640);
x_641 = l_String_toSubstring_x27(x_640);
x_642 = l_Lean_Name_mkStr1(x_640);
lean_inc(x_642);
x_643 = l_Lean_addMacroScope(x_639, x_642, x_625);
x_644 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_644, 0, x_642);
lean_ctor_set(x_644, 1, x_613);
x_645 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_628);
x_646 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_646, 0, x_601);
lean_ctor_set(x_646, 1, x_641);
lean_ctor_set(x_646, 2, x_643);
lean_ctor_set(x_646, 3, x_645);
x_647 = lean_box(0);
x_648 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_648, 0, x_646);
lean_ctor_set(x_648, 1, x_647);
x_649 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_649, 0, x_637);
lean_ctor_set(x_649, 1, x_648);
x_650 = lean_array_size(x_5);
x_651 = lean_unsigned_to_nat(0u);
x_652 = lean_usize_of_nat(x_651);
x_653 = l_Array_mapMUnsafe_map___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(x_650, x_652, x_5, x_54, x_55, x_606);
if (lean_obj_tag(x_653) == 0)
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; uint8_t x_663; 
x_654 = lean_ctor_get(x_653, 0);
lean_inc(x_654);
x_655 = lean_ctor_get(x_653, 1);
lean_inc(x_655);
lean_dec(x_653);
x_656 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_656, 0, x_624);
lean_ctor_set(x_656, 1, x_626);
lean_ctor_set(x_656, 2, x_627);
lean_ctor_set(x_656, 3, x_629);
x_657 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_657, 0, x_636);
lean_ctor_set(x_657, 1, x_649);
x_658 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_658, 0, x_656);
lean_ctor_set(x_658, 1, x_657);
x_659 = lean_box(0);
x_660 = l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(x_658, x_659);
x_661 = l_Array_empty(lean_box(0));
x_662 = lean_array_get_size(x_654);
x_663 = lean_nat_dec_lt(x_651, x_662);
if (x_663 == 0)
{
lean_dec(x_662);
lean_dec(x_654);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_659;
x_40 = x_655;
x_41 = x_54;
x_42 = x_660;
x_43 = x_661;
goto block_51;
}
else
{
uint8_t x_664; 
x_664 = lean_nat_dec_le(x_662, x_662);
if (x_664 == 0)
{
lean_dec(x_662);
lean_dec(x_654);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_659;
x_40 = x_655;
x_41 = x_54;
x_42 = x_660;
x_43 = x_661;
goto block_51;
}
else
{
size_t x_665; lean_object* x_666; 
x_665 = lean_usize_of_nat(x_662);
lean_dec(x_662);
x_666 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__6(x_654, x_652, x_665, x_661);
lean_dec(x_654);
x_36 = x_52;
x_37 = x_53;
x_38 = x_55;
x_39 = x_659;
x_40 = x_655;
x_41 = x_54;
x_42 = x_660;
x_43 = x_666;
goto block_51;
}
}
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; 
lean_dec(x_649);
lean_dec(x_636);
lean_dec(x_629);
lean_dec(x_627);
lean_dec(x_626);
lean_dec(x_624);
lean_dec(x_54);
lean_dec(x_35);
lean_dec(x_4);
lean_dec(x_3);
x_667 = lean_ctor_get(x_653, 0);
lean_inc(x_667);
x_668 = lean_ctor_get(x_653, 1);
lean_inc(x_668);
if (lean_is_exclusive(x_653)) {
 lean_ctor_release(x_653, 0);
 lean_ctor_release(x_653, 1);
 x_669 = x_653;
} else {
 lean_dec_ref(x_653);
 x_669 = lean_box(0);
}
if (lean_is_scalar(x_669)) {
 x_670 = lean_alloc_ctor(1, 2, 0);
} else {
 x_670 = x_669;
}
lean_ctor_set(x_670, 0, x_667);
lean_ctor_set(x_670, 1, x_668);
return x_670;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(x_7, x_8, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_elem___at___List_removeAll___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at___List_removeAll___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_removeAll___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_mapTR_loop___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SolveByElim_mkAssumptionSet_spec__6(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_SolveByElim_mkAssumptionSet(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
return x_13;
}
}
lean_object* initialize_Init_Data_Sum(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_LabelAttribute(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Backtrack(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Constructor(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Repeat(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Symm(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_SolveByElim(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Sum(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LabelAttribute(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Backtrack(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Constructor(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Repeat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Symm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig = _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig();
lean_mark_persistent(l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
