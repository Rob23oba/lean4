// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Core
// Imports: Init.Grind.Util Lean.Meta.LitValues Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Inv Lean.Meta.Tactic.Grind.PP Lean.Meta.Tactic.Grind.Ctor Lean.Meta.Tactic.Grind.Util Lean.Meta.Tactic.Grind.Beta Lean.Meta.Tactic.Grind.Internalize Lean.Meta.Tactic.Grind.Simp
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
lean_object* l_Lean_Meta_Grind_getParents___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_checkOffsetEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Array_reverse(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_checkCommRingEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_process_ring_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_checkCutsatEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_setENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Grind_getFalseExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_propagateUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_propagateBeta_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateCommRingDiseqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_propagateBeta_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateBetaEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getFnRoots(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ppENodeRef___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_Meta_Grind_isCongrRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_propagateBeta_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_Grind_propagateBeta_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateCutsatDiseqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_propagateBeta_spec__6_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instBEqCongrKey___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_Grind_propagateBeta_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Array_back_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addCongrTable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_Grind_propagateBeta_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_propagateBeta_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_checkInvariants(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_process_cutsat_eq_lit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getEqcLambdas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_Grind_propagateBeta_spec__4_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_checkOffsetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instHashableCongrKey(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_copyParentsTo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_ppState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_propagateBeta_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_process_new_offset_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_checkCutsatEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markAsInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isNatNum(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getTrueExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_Grind_propagateBeta_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
lean_object* l_Lean_MVarId_isAssigned___at___Lean_Meta_Grind_closeGoal_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_mkEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_checkCommRingEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCutsat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_Grind_propagateBeta_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_process_new_offset_eq_lit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_process_cutsat_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_Grind_resetParentsOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_grind_process_new_facts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_propagateBeta_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getEqc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object**);
uint8_t l_Lean_Meta_Grind_isNum(lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_st_ref_get(x_5, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
x_17 = l_Lean_Meta_Grind_Goal_getENode(x_15, x_1, x_11, x_12, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_47; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_47 = lean_ctor_get(x_18, 4);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_12;
x_28 = x_19;
goto block_46;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_56; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_56 = lean_ctor_get_uint8(x_18, sizeof(void*)*13);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_box(1);
x_58 = lean_unbox(x_57);
x_50 = x_58;
goto block_55;
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_box(0);
x_60 = lean_unbox(x_59);
x_50 = x_60;
goto block_55;
}
block_55:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_inc(x_1);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_1);
x_52 = lean_ctor_get(x_18, 5);
lean_inc(x_52);
x_53 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go(x_48, x_50, x_51, x_52, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_12;
x_28 = x_54;
goto block_46;
}
else
{
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_53;
}
}
}
block_46:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_29 = lean_ctor_get(x_18, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_18, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_18, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_18, 6);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_18, sizeof(void*)*13 + 1);
x_35 = lean_ctor_get_uint8(x_18, sizeof(void*)*13 + 2);
x_36 = lean_ctor_get_uint8(x_18, sizeof(void*)*13 + 3);
x_37 = lean_ctor_get_uint8(x_18, sizeof(void*)*13 + 4);
x_38 = lean_ctor_get(x_18, 7);
lean_inc(x_38);
x_39 = lean_ctor_get(x_18, 8);
lean_inc(x_39);
x_40 = lean_ctor_get(x_18, 9);
lean_inc(x_40);
x_41 = lean_ctor_get(x_18, 10);
lean_inc(x_41);
x_42 = lean_ctor_get(x_18, 11);
lean_inc(x_42);
x_43 = lean_ctor_get(x_18, 12);
lean_inc(x_43);
lean_dec(x_18);
x_44 = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(x_44, 0, x_29);
lean_ctor_set(x_44, 1, x_30);
lean_ctor_set(x_44, 2, x_31);
lean_ctor_set(x_44, 3, x_32);
lean_ctor_set(x_44, 4, x_3);
lean_ctor_set(x_44, 5, x_4);
lean_ctor_set(x_44, 6, x_33);
lean_ctor_set(x_44, 7, x_38);
lean_ctor_set(x_44, 8, x_39);
lean_ctor_set(x_44, 9, x_40);
lean_ctor_set(x_44, 10, x_41);
lean_ctor_set(x_44, 11, x_42);
lean_ctor_set(x_44, 12, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*13, x_2);
lean_ctor_set_uint8(x_44, sizeof(void*)*13 + 1, x_34);
lean_ctor_set_uint8(x_44, sizeof(void*)*13 + 2, x_35);
lean_ctor_set_uint8(x_44, sizeof(void*)*13 + 3, x_36);
lean_ctor_set_uint8(x_44, sizeof(void*)*13 + 4, x_37);
x_45 = l_Lean_Meta_Grind_setENode(x_1, x_44, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
return x_45;
}
}
else
{
uint8_t x_61; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_17);
if (x_61 == 0)
{
return x_17;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_17, 0);
x_63 = lean_ctor_get(x_17, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_17);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_unbox(x_11);
x_14 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go(x_1, x_13, x_12, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 4);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_50; lean_object* x_51; uint8_t x_95; 
lean_dec(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_box(0);
x_95 = l_Lean_Expr_isApp(x_12);
if (x_95 == 0)
{
x_50 = x_95;
x_51 = x_17;
goto block_94;
}
else
{
lean_object* x_96; 
lean_inc(x_12);
x_96 = l_Lean_Meta_Grind_isCongrRoot___redArg(x_12, x_3, x_9, x_10, x_17);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_unbox(x_97);
lean_dec(x_97);
x_50 = x_99;
x_51 = x_98;
goto block_94;
}
else
{
uint8_t x_100; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
x_100 = !lean_is_exclusive(x_96);
if (x_100 == 0)
{
return x_96;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_96, 0);
x_102 = lean_ctor_get(x_96, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_96);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
block_49:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_22 = lean_st_ref_take(x_20, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_23, 4);
lean_inc(x_29);
lean_inc(x_27);
x_30 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instBEqCongrKey___lam__0___boxed), 3, 1);
lean_closure_set(x_30, 0, x_27);
lean_inc(x_27);
x_31 = l_Lean_Meta_Grind_instHashableCongrKey(x_27);
x_32 = lean_ctor_get(x_23, 5);
lean_inc(x_32);
x_33 = l_Lean_PersistentHashMap_erase___redArg(x_30, x_31, x_32, x_12);
x_34 = lean_ctor_get(x_23, 6);
lean_inc(x_34);
x_35 = lean_ctor_get(x_23, 7);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_23, sizeof(void*)*16);
x_37 = lean_ctor_get(x_23, 8);
lean_inc(x_37);
x_38 = lean_ctor_get(x_23, 9);
lean_inc(x_38);
x_39 = lean_ctor_get(x_23, 10);
lean_inc(x_39);
x_40 = lean_ctor_get(x_23, 11);
lean_inc(x_40);
x_41 = lean_ctor_get(x_23, 12);
lean_inc(x_41);
x_42 = lean_ctor_get(x_23, 13);
lean_inc(x_42);
x_43 = lean_ctor_get(x_23, 14);
lean_inc(x_43);
x_44 = lean_ctor_get(x_23, 15);
lean_inc(x_44);
lean_dec(x_23);
x_45 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_45, 0, x_25);
lean_ctor_set(x_45, 1, x_26);
lean_ctor_set(x_45, 2, x_27);
lean_ctor_set(x_45, 3, x_28);
lean_ctor_set(x_45, 4, x_29);
lean_ctor_set(x_45, 5, x_33);
lean_ctor_set(x_45, 6, x_34);
lean_ctor_set(x_45, 7, x_35);
lean_ctor_set(x_45, 8, x_37);
lean_ctor_set(x_45, 9, x_38);
lean_ctor_set(x_45, 10, x_39);
lean_ctor_set(x_45, 11, x_40);
lean_ctor_set(x_45, 12, x_41);
lean_ctor_set(x_45, 13, x_42);
lean_ctor_set(x_45, 14, x_43);
lean_ctor_set(x_45, 15, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*16, x_36);
x_46 = lean_st_ref_set(x_20, x_45, x_24);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_1 = x_19;
x_2 = x_14;
x_11 = x_47;
goto _start;
}
block_94:
{
if (x_50 == 0)
{
lean_dec(x_18);
lean_dec(x_12);
x_1 = x_19;
x_2 = x_14;
x_11 = x_51;
goto _start;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_53 = lean_mk_string_unchecked("grind", 5, 5);
x_54 = lean_mk_string_unchecked("debug", 5, 5);
x_55 = lean_mk_string_unchecked("parent", 6, 6);
x_56 = l_Lean_Name_mkStr3(x_53, x_54, x_55);
lean_inc(x_56);
x_57 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_56, x_9, x_51);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_56);
lean_dec(x_18);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_20 = x_3;
x_21 = x_60;
goto block_49;
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 1);
x_63 = lean_ctor_get(x_57, 0);
lean_dec(x_63);
x_64 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_mk_string_unchecked("remove: ", 8, 8);
x_67 = l_Lean_stringToMessageData(x_66);
lean_dec(x_66);
lean_inc(x_12);
x_68 = l_Lean_MessageData_ofExpr(x_12);
lean_ctor_set_tag(x_57, 7);
lean_ctor_set(x_57, 1, x_68);
lean_ctor_set(x_57, 0, x_67);
x_69 = lean_mk_string_unchecked("", 0, 0);
x_70 = l_Lean_stringToMessageData(x_69);
lean_dec(x_69);
if (lean_is_scalar(x_18)) {
 x_71 = lean_alloc_ctor(7, 2, 0);
} else {
 x_71 = x_18;
 lean_ctor_set_tag(x_71, 7);
}
lean_ctor_set(x_71, 0, x_57);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_56, x_71, x_7, x_8, x_9, x_10, x_65);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_20 = x_3;
x_21 = x_73;
goto block_49;
}
else
{
uint8_t x_74; 
lean_free_object(x_57);
lean_dec(x_56);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
x_74 = !lean_is_exclusive(x_64);
if (x_74 == 0)
{
return x_64;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_64, 0);
x_76 = lean_ctor_get(x_64, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_64);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_57, 1);
lean_inc(x_78);
lean_dec(x_57);
x_79 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_mk_string_unchecked("remove: ", 8, 8);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
lean_inc(x_12);
x_83 = l_Lean_MessageData_ofExpr(x_12);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_mk_string_unchecked("", 0, 0);
x_86 = l_Lean_stringToMessageData(x_85);
lean_dec(x_85);
if (lean_is_scalar(x_18)) {
 x_87 = lean_alloc_ctor(7, 2, 0);
} else {
 x_87 = x_18;
 lean_ctor_set_tag(x_87, 7);
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_56, x_87, x_7, x_8, x_9, x_10, x_80);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_20 = x_3;
x_21 = x_89;
goto block_49;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_56);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
x_90 = lean_ctor_get(x_79, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_79, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_92 = x_79;
} else {
 lean_dec_ref(x_79);
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
else
{
lean_dec(x_14);
lean_dec(x_12);
return x_15;
}
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_1);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_11);
return x_105;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 4);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_50; lean_object* x_51; uint8_t x_95; 
lean_dec(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_box(0);
x_95 = l_Lean_Expr_isApp(x_12);
if (x_95 == 0)
{
x_50 = x_95;
x_51 = x_17;
goto block_94;
}
else
{
lean_object* x_96; 
lean_inc(x_12);
x_96 = l_Lean_Meta_Grind_isCongrRoot___redArg(x_12, x_3, x_9, x_10, x_17);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_unbox(x_97);
lean_dec(x_97);
x_50 = x_99;
x_51 = x_98;
goto block_94;
}
else
{
uint8_t x_100; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
x_100 = !lean_is_exclusive(x_96);
if (x_100 == 0)
{
return x_96;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_96, 0);
x_102 = lean_ctor_get(x_96, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_96);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
block_49:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_22 = lean_st_ref_take(x_20, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_23, 4);
lean_inc(x_29);
lean_inc(x_27);
x_30 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instBEqCongrKey___lam__0___boxed), 3, 1);
lean_closure_set(x_30, 0, x_27);
lean_inc(x_27);
x_31 = l_Lean_Meta_Grind_instHashableCongrKey(x_27);
x_32 = lean_ctor_get(x_23, 5);
lean_inc(x_32);
x_33 = l_Lean_PersistentHashMap_erase___redArg(x_30, x_31, x_32, x_12);
x_34 = lean_ctor_get(x_23, 6);
lean_inc(x_34);
x_35 = lean_ctor_get(x_23, 7);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_23, sizeof(void*)*16);
x_37 = lean_ctor_get(x_23, 8);
lean_inc(x_37);
x_38 = lean_ctor_get(x_23, 9);
lean_inc(x_38);
x_39 = lean_ctor_get(x_23, 10);
lean_inc(x_39);
x_40 = lean_ctor_get(x_23, 11);
lean_inc(x_40);
x_41 = lean_ctor_get(x_23, 12);
lean_inc(x_41);
x_42 = lean_ctor_get(x_23, 13);
lean_inc(x_42);
x_43 = lean_ctor_get(x_23, 14);
lean_inc(x_43);
x_44 = lean_ctor_get(x_23, 15);
lean_inc(x_44);
lean_dec(x_23);
x_45 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_45, 0, x_25);
lean_ctor_set(x_45, 1, x_26);
lean_ctor_set(x_45, 2, x_27);
lean_ctor_set(x_45, 3, x_28);
lean_ctor_set(x_45, 4, x_29);
lean_ctor_set(x_45, 5, x_33);
lean_ctor_set(x_45, 6, x_34);
lean_ctor_set(x_45, 7, x_35);
lean_ctor_set(x_45, 8, x_37);
lean_ctor_set(x_45, 9, x_38);
lean_ctor_set(x_45, 10, x_39);
lean_ctor_set(x_45, 11, x_40);
lean_ctor_set(x_45, 12, x_41);
lean_ctor_set(x_45, 13, x_42);
lean_ctor_set(x_45, 14, x_43);
lean_ctor_set(x_45, 15, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*16, x_36);
x_46 = lean_st_ref_set(x_20, x_45, x_24);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(x_19, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_47);
return x_48;
}
block_94:
{
if (x_50 == 0)
{
lean_object* x_52; 
lean_dec(x_18);
lean_dec(x_12);
x_52 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(x_19, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_51);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_53 = lean_mk_string_unchecked("grind", 5, 5);
x_54 = lean_mk_string_unchecked("debug", 5, 5);
x_55 = lean_mk_string_unchecked("parent", 6, 6);
x_56 = l_Lean_Name_mkStr3(x_53, x_54, x_55);
lean_inc(x_56);
x_57 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_56, x_9, x_51);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_56);
lean_dec(x_18);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_20 = x_3;
x_21 = x_60;
goto block_49;
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 1);
x_63 = lean_ctor_get(x_57, 0);
lean_dec(x_63);
x_64 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_mk_string_unchecked("remove: ", 8, 8);
x_67 = l_Lean_stringToMessageData(x_66);
lean_dec(x_66);
lean_inc(x_12);
x_68 = l_Lean_MessageData_ofExpr(x_12);
lean_ctor_set_tag(x_57, 7);
lean_ctor_set(x_57, 1, x_68);
lean_ctor_set(x_57, 0, x_67);
x_69 = lean_mk_string_unchecked("", 0, 0);
x_70 = l_Lean_stringToMessageData(x_69);
lean_dec(x_69);
if (lean_is_scalar(x_18)) {
 x_71 = lean_alloc_ctor(7, 2, 0);
} else {
 x_71 = x_18;
 lean_ctor_set_tag(x_71, 7);
}
lean_ctor_set(x_71, 0, x_57);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_56, x_71, x_7, x_8, x_9, x_10, x_65);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_20 = x_3;
x_21 = x_73;
goto block_49;
}
else
{
uint8_t x_74; 
lean_free_object(x_57);
lean_dec(x_56);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
x_74 = !lean_is_exclusive(x_64);
if (x_74 == 0)
{
return x_64;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_64, 0);
x_76 = lean_ctor_get(x_64, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_64);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_57, 1);
lean_inc(x_78);
lean_dec(x_57);
x_79 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_mk_string_unchecked("remove: ", 8, 8);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
lean_inc(x_12);
x_83 = l_Lean_MessageData_ofExpr(x_12);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_mk_string_unchecked("", 0, 0);
x_86 = l_Lean_stringToMessageData(x_85);
lean_dec(x_85);
if (lean_is_scalar(x_18)) {
 x_87 = lean_alloc_ctor(7, 2, 0);
} else {
 x_87 = x_18;
 lean_ctor_set_tag(x_87, 7);
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_56, x_87, x_7, x_8, x_9, x_10, x_80);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_20 = x_3;
x_21 = x_89;
goto block_49;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_56);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
x_90 = lean_ctor_get(x_79, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_79, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_92 = x_79;
} else {
 lean_dec_ref(x_79);
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
else
{
lean_dec(x_14);
lean_dec(x_12);
return x_15;
}
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_1);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_11);
return x_105;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lean_Meta_Grind_getParents___redArg(x_1, x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
lean_inc(x_12);
x_15 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(x_14, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_12);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 4);
lean_inc(x_14);
lean_dec(x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_37; lean_object* x_38; uint8_t x_82; 
lean_dec(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_box(0);
x_82 = l_Lean_Expr_isApp(x_12);
if (x_82 == 0)
{
x_37 = x_82;
x_38 = x_17;
goto block_81;
}
else
{
lean_object* x_83; 
lean_inc(x_12);
x_83 = l_Lean_Meta_Grind_isCongrRoot___redArg(x_12, x_3, x_9, x_10, x_17);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_unbox(x_84);
lean_dec(x_84);
x_37 = x_86;
x_38 = x_85;
goto block_81;
}
else
{
uint8_t x_87; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_87 = !lean_is_exclusive(x_83);
if (x_87 == 0)
{
return x_83;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_83, 0);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_83);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
block_36:
{
lean_object* x_29; 
x_29 = l_Lean_Meta_Grind_addCongrTable(x_12, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_1 = x_19;
x_2 = x_14;
x_11 = x_30;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
block_81:
{
if (x_37 == 0)
{
lean_dec(x_18);
lean_dec(x_12);
x_1 = x_19;
x_2 = x_14;
x_11 = x_38;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_40 = lean_mk_string_unchecked("grind", 5, 5);
x_41 = lean_mk_string_unchecked("debug", 5, 5);
x_42 = lean_mk_string_unchecked("parent", 6, 6);
x_43 = l_Lean_Name_mkStr3(x_40, x_41, x_42);
lean_inc(x_43);
x_44 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_43, x_9, x_38);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_43);
lean_dec(x_18);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_20 = x_3;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = x_9;
x_27 = x_10;
x_28 = x_47;
goto block_36;
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 1);
x_50 = lean_ctor_get(x_44, 0);
lean_dec(x_50);
x_51 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_mk_string_unchecked("reinsert: ", 10, 10);
x_54 = l_Lean_stringToMessageData(x_53);
lean_dec(x_53);
lean_inc(x_12);
x_55 = l_Lean_MessageData_ofExpr(x_12);
lean_ctor_set_tag(x_44, 7);
lean_ctor_set(x_44, 1, x_55);
lean_ctor_set(x_44, 0, x_54);
x_56 = lean_mk_string_unchecked("", 0, 0);
x_57 = l_Lean_stringToMessageData(x_56);
lean_dec(x_56);
if (lean_is_scalar(x_18)) {
 x_58 = lean_alloc_ctor(7, 2, 0);
} else {
 x_58 = x_18;
 lean_ctor_set_tag(x_58, 7);
}
lean_ctor_set(x_58, 0, x_44);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_43, x_58, x_7, x_8, x_9, x_10, x_52);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_20 = x_3;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = x_9;
x_27 = x_10;
x_28 = x_60;
goto block_36;
}
else
{
uint8_t x_61; 
lean_free_object(x_44);
lean_dec(x_43);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_61 = !lean_is_exclusive(x_51);
if (x_61 == 0)
{
return x_51;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_51, 0);
x_63 = lean_ctor_get(x_51, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_51);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_44, 1);
lean_inc(x_65);
lean_dec(x_44);
x_66 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_mk_string_unchecked("reinsert: ", 10, 10);
x_69 = l_Lean_stringToMessageData(x_68);
lean_dec(x_68);
lean_inc(x_12);
x_70 = l_Lean_MessageData_ofExpr(x_12);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_mk_string_unchecked("", 0, 0);
x_73 = l_Lean_stringToMessageData(x_72);
lean_dec(x_72);
if (lean_is_scalar(x_18)) {
 x_74 = lean_alloc_ctor(7, 2, 0);
} else {
 x_74 = x_18;
 lean_ctor_set_tag(x_74, 7);
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_43, x_74, x_7, x_8, x_9, x_10, x_67);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_20 = x_3;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = x_9;
x_27 = x_10;
x_28 = x_76;
goto block_36;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_43);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_77 = lean_ctor_get(x_66, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_66, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_79 = x_66;
} else {
 lean_dec_ref(x_66);
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
}
}
else
{
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_15;
}
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_1);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_11);
return x_92;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 4);
lean_inc(x_14);
lean_dec(x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_37; lean_object* x_38; uint8_t x_82; 
lean_dec(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_box(0);
x_82 = l_Lean_Expr_isApp(x_12);
if (x_82 == 0)
{
x_37 = x_82;
x_38 = x_17;
goto block_81;
}
else
{
lean_object* x_83; 
lean_inc(x_12);
x_83 = l_Lean_Meta_Grind_isCongrRoot___redArg(x_12, x_3, x_9, x_10, x_17);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_unbox(x_84);
lean_dec(x_84);
x_37 = x_86;
x_38 = x_85;
goto block_81;
}
else
{
uint8_t x_87; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_87 = !lean_is_exclusive(x_83);
if (x_87 == 0)
{
return x_83;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_83, 0);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_83);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
block_36:
{
lean_object* x_29; 
x_29 = l_Lean_Meta_Grind_addCongrTable(x_12, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0(x_19, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
block_81:
{
if (x_37 == 0)
{
lean_object* x_39; 
lean_dec(x_18);
lean_dec(x_12);
x_39 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0(x_19, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_40 = lean_mk_string_unchecked("grind", 5, 5);
x_41 = lean_mk_string_unchecked("debug", 5, 5);
x_42 = lean_mk_string_unchecked("parent", 6, 6);
x_43 = l_Lean_Name_mkStr3(x_40, x_41, x_42);
lean_inc(x_43);
x_44 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_43, x_9, x_38);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_43);
lean_dec(x_18);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_20 = x_3;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = x_9;
x_27 = x_10;
x_28 = x_47;
goto block_36;
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 1);
x_50 = lean_ctor_get(x_44, 0);
lean_dec(x_50);
x_51 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_mk_string_unchecked("reinsert: ", 10, 10);
x_54 = l_Lean_stringToMessageData(x_53);
lean_dec(x_53);
lean_inc(x_12);
x_55 = l_Lean_MessageData_ofExpr(x_12);
lean_ctor_set_tag(x_44, 7);
lean_ctor_set(x_44, 1, x_55);
lean_ctor_set(x_44, 0, x_54);
x_56 = lean_mk_string_unchecked("", 0, 0);
x_57 = l_Lean_stringToMessageData(x_56);
lean_dec(x_56);
if (lean_is_scalar(x_18)) {
 x_58 = lean_alloc_ctor(7, 2, 0);
} else {
 x_58 = x_18;
 lean_ctor_set_tag(x_58, 7);
}
lean_ctor_set(x_58, 0, x_44);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_43, x_58, x_7, x_8, x_9, x_10, x_52);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_20 = x_3;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = x_9;
x_27 = x_10;
x_28 = x_60;
goto block_36;
}
else
{
uint8_t x_61; 
lean_free_object(x_44);
lean_dec(x_43);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_61 = !lean_is_exclusive(x_51);
if (x_61 == 0)
{
return x_51;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_51, 0);
x_63 = lean_ctor_get(x_51, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_51);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_44, 1);
lean_inc(x_65);
lean_dec(x_44);
x_66 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_mk_string_unchecked("reinsert: ", 10, 10);
x_69 = l_Lean_stringToMessageData(x_68);
lean_dec(x_68);
lean_inc(x_12);
x_70 = l_Lean_MessageData_ofExpr(x_12);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_mk_string_unchecked("", 0, 0);
x_73 = l_Lean_stringToMessageData(x_72);
lean_dec(x_72);
if (lean_is_scalar(x_18)) {
 x_74 = lean_alloc_ctor(7, 2, 0);
} else {
 x_74 = x_18;
 lean_ctor_set_tag(x_74, 7);
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_43, x_74, x_7, x_8, x_9, x_10, x_67);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_20 = x_3;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = x_9;
x_27 = x_10;
x_28 = x_76;
goto block_36;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_43);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_77 = lean_ctor_get(x_66, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_66, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_79 = x_66;
} else {
 lean_dec_ref(x_66);
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
}
}
else
{
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_15;
}
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_1);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_11);
return x_92;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_MVarId_isAssigned___at___Lean_Meta_Grind_closeGoal_spec__0(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Meta_Grind_getTrueExpr(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_Lean_Meta_Grind_mkEqFalseProof(x_19, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_Grind_getTrueExpr(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_Grind_getFalseExpr(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_26);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_mk_string_unchecked("Eq", 2, 2);
x_32 = lean_mk_string_unchecked("mp", 2, 2);
x_33 = l_Lean_Name_mkStr2(x_31, x_32);
x_34 = lean_box(0);
x_35 = lean_box(0);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_35);
lean_ctor_set(x_27, 0, x_34);
x_36 = l_Lean_Expr_const___override(x_33, x_27);
x_37 = lean_mk_string_unchecked("True", 4, 4);
x_38 = lean_mk_string_unchecked("intro", 5, 5);
x_39 = l_Lean_Name_mkStr2(x_37, x_38);
x_40 = l_Lean_Expr_const___override(x_39, x_35);
x_41 = l_Lean_mkApp4(x_36, x_25, x_29, x_22, x_40);
x_42 = l_Lean_Meta_Grind_closeGoal(x_41, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_43 = lean_ctor_get(x_27, 0);
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_27);
x_45 = lean_mk_string_unchecked("Eq", 2, 2);
x_46 = lean_mk_string_unchecked("mp", 2, 2);
x_47 = l_Lean_Name_mkStr2(x_45, x_46);
x_48 = lean_box(0);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Expr_const___override(x_47, x_50);
x_52 = lean_mk_string_unchecked("True", 4, 4);
x_53 = lean_mk_string_unchecked("intro", 5, 5);
x_54 = l_Lean_Name_mkStr2(x_52, x_53);
x_55 = l_Lean_Expr_const___override(x_54, x_49);
x_56 = l_Lean_mkApp4(x_51, x_25, x_43, x_22, x_55);
x_57 = l_Lean_Meta_Grind_closeGoal(x_56, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_44);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_21);
if (x_58 == 0)
{
return x_21;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_21, 0);
x_60 = lean_ctor_get(x_21, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_21);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_14);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_14, 0);
lean_dec(x_63);
x_64 = lean_box(0);
lean_ctor_set(x_14, 0, x_64);
return x_14;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_14, 1);
lean_inc(x_65);
lean_dec(x_14);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_Meta_mkEq(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = lean_grind_mk_eq_proof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
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
lean_inc(x_7);
lean_inc(x_13);
x_18 = l_Lean_Meta_mkDecide(x_13, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_mk_string_unchecked("eq_false_of_decide", 18, 18);
x_22 = lean_box(0);
x_23 = lean_mk_string_unchecked("Eq", 2, 2);
x_24 = lean_mk_string_unchecked("refl", 4, 4);
lean_inc(x_23);
x_25 = l_Lean_Name_mkStr2(x_23, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = l_Lean_Level_ofNat(x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
x_29 = lean_mk_string_unchecked("Bool", 4, 4);
lean_inc(x_29);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = lean_mk_string_unchecked("false", 5, 5);
x_32 = l_Lean_Name_mkStr2(x_29, x_31);
x_33 = l_Lean_Meta_Grind_getFalseExpr(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = l_Lean_Name_mkStr1(x_21);
x_38 = l_Lean_Expr_const___override(x_25, x_28);
x_39 = l_Lean_Expr_const___override(x_30, x_22);
x_40 = l_Lean_Expr_const___override(x_32, x_22);
x_41 = l_Lean_Expr_const___override(x_37, x_22);
x_42 = l_Lean_Expr_appArg_x21(x_19);
lean_dec(x_19);
x_43 = l_Lean_mkAppB(x_38, x_39, x_40);
lean_inc(x_13);
x_44 = l_Lean_mkApp3(x_41, x_13, x_42, x_43);
x_45 = lean_mk_string_unchecked("mp", 2, 2);
x_46 = l_Lean_Name_mkStr2(x_23, x_45);
x_47 = lean_box(0);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 1, x_22);
lean_ctor_set(x_33, 0, x_47);
x_48 = l_Lean_Expr_const___override(x_46, x_33);
x_49 = l_Lean_mkApp4(x_48, x_13, x_35, x_44, x_16);
x_50 = l_Lean_Meta_Grind_closeGoal(x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_51 = lean_ctor_get(x_33, 0);
x_52 = lean_ctor_get(x_33, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_33);
x_53 = l_Lean_Name_mkStr1(x_21);
x_54 = l_Lean_Expr_const___override(x_25, x_28);
x_55 = l_Lean_Expr_const___override(x_30, x_22);
x_56 = l_Lean_Expr_const___override(x_32, x_22);
x_57 = l_Lean_Expr_const___override(x_53, x_22);
x_58 = l_Lean_Expr_appArg_x21(x_19);
lean_dec(x_19);
x_59 = l_Lean_mkAppB(x_54, x_55, x_56);
lean_inc(x_13);
x_60 = l_Lean_mkApp3(x_57, x_13, x_58, x_59);
x_61 = lean_mk_string_unchecked("mp", 2, 2);
x_62 = l_Lean_Name_mkStr2(x_23, x_61);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_22);
x_65 = l_Lean_Expr_const___override(x_62, x_64);
x_66 = l_Lean_mkApp4(x_65, x_13, x_51, x_60, x_16);
x_67 = l_Lean_Meta_Grind_closeGoal(x_66, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_52);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_67;
}
}
else
{
uint8_t x_68; 
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
x_68 = !lean_is_exclusive(x_18);
if (x_68 == 0)
{
return x_18;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_18, 0);
x_70 = lean_ctor_get(x_18, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_18);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_72 = !lean_is_exclusive(x_15);
if (x_72 == 0)
{
return x_15;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_15, 0);
x_74 = lean_ctor_get(x_15, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_15);
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
x_76 = !lean_is_exclusive(x_12);
if (x_76 == 0)
{
return x_12;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_12, 0);
x_78 = lean_ctor_get(x_12, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_12);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 4);
lean_inc(x_15);
lean_dec(x_3);
lean_inc(x_1);
x_16 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_4, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_13);
x_22 = l_Lean_Meta_Grind_Goal_getENode(x_20, x_13, x_10, x_11, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = lean_ctor_get(x_23, 9);
lean_inc(x_26);
x_27 = lean_nat_dec_lt(x_26, x_1);
lean_dec(x_26);
if (x_27 == 0)
{
lean_dec(x_23);
lean_dec(x_13);
x_2 = x_25;
x_3 = x_15;
x_12 = x_24;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_23, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_23, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_23, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_23, 5);
lean_inc(x_34);
x_35 = lean_ctor_get_uint8(x_23, sizeof(void*)*13);
x_36 = lean_ctor_get(x_23, 6);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_23, sizeof(void*)*13 + 1);
x_38 = lean_ctor_get_uint8(x_23, sizeof(void*)*13 + 2);
x_39 = lean_ctor_get_uint8(x_23, sizeof(void*)*13 + 3);
x_40 = lean_ctor_get_uint8(x_23, sizeof(void*)*13 + 4);
x_41 = lean_ctor_get(x_23, 7);
lean_inc(x_41);
x_42 = lean_ctor_get(x_23, 8);
lean_inc(x_42);
x_43 = lean_ctor_get(x_23, 10);
lean_inc(x_43);
x_44 = lean_ctor_get(x_23, 11);
lean_inc(x_44);
x_45 = lean_ctor_get(x_23, 12);
lean_inc(x_45);
lean_dec(x_23);
lean_inc(x_1);
x_46 = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(x_46, 0, x_29);
lean_ctor_set(x_46, 1, x_30);
lean_ctor_set(x_46, 2, x_31);
lean_ctor_set(x_46, 3, x_32);
lean_ctor_set(x_46, 4, x_33);
lean_ctor_set(x_46, 5, x_34);
lean_ctor_set(x_46, 6, x_36);
lean_ctor_set(x_46, 7, x_41);
lean_ctor_set(x_46, 8, x_42);
lean_ctor_set(x_46, 9, x_1);
lean_ctor_set(x_46, 10, x_43);
lean_ctor_set(x_46, 11, x_44);
lean_ctor_set(x_46, 12, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*13, x_35);
lean_ctor_set_uint8(x_46, sizeof(void*)*13 + 1, x_37);
lean_ctor_set_uint8(x_46, sizeof(void*)*13 + 2, x_38);
lean_ctor_set_uint8(x_46, sizeof(void*)*13 + 3, x_39);
lean_ctor_set_uint8(x_46, sizeof(void*)*13 + 4, x_40);
lean_inc(x_13);
x_47 = l_Lean_Meta_Grind_setENode(x_13, x_46, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_48);
lean_dec(x_13);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_2 = x_25;
x_3 = x_15;
x_12 = x_50;
goto _start;
}
else
{
uint8_t x_52; 
lean_dec(x_15);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
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
uint8_t x_56; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_22);
if (x_56 == 0)
{
return x_22;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_22, 0);
x_58 = lean_ctor_get(x_22, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_22);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_1);
return x_16;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_1);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_2);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_12);
return x_61;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_st_ref_get(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_Grind_getParents___redArg(x_1, x_2, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_12, 12);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(x_18, x_19, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_checkOffsetEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_16; 
x_16 = lean_ctor_get(x_2, 10);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
lean_inc(x_17);
x_18 = l_Lean_Meta_Grind_isNatNum(x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_1);
x_12 = x_11;
goto block_15;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_1, 10);
lean_inc(x_19);
lean_dec(x_1);
if (lean_obj_tag(x_19) == 0)
{
lean_dec(x_17);
x_12 = x_11;
goto block_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_11);
return x_22;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_2);
x_23 = lean_ctor_get(x_1, 10);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
lean_inc(x_25);
x_26 = l_Lean_Meta_Grind_isNatNum(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_24);
x_27 = lean_st_ref_get(x_3, x_11);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_Grind_Goal_getENode(x_28, x_25, x_9, x_10, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_31, 5);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_31, sizeof(void*)*13);
x_40 = lean_ctor_get(x_31, 6);
lean_inc(x_40);
x_41 = lean_ctor_get_uint8(x_31, sizeof(void*)*13 + 1);
x_42 = lean_ctor_get_uint8(x_31, sizeof(void*)*13 + 2);
x_43 = lean_ctor_get_uint8(x_31, sizeof(void*)*13 + 3);
x_44 = lean_ctor_get_uint8(x_31, sizeof(void*)*13 + 4);
x_45 = lean_ctor_get(x_31, 7);
lean_inc(x_45);
x_46 = lean_ctor_get(x_31, 8);
lean_inc(x_46);
x_47 = lean_ctor_get(x_31, 9);
lean_inc(x_47);
x_48 = lean_ctor_get(x_31, 11);
lean_inc(x_48);
x_49 = lean_ctor_get(x_31, 12);
lean_inc(x_49);
lean_dec(x_31);
lean_inc(x_33);
x_50 = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(x_50, 0, x_33);
lean_ctor_set(x_50, 1, x_34);
lean_ctor_set(x_50, 2, x_35);
lean_ctor_set(x_50, 3, x_36);
lean_ctor_set(x_50, 4, x_37);
lean_ctor_set(x_50, 5, x_38);
lean_ctor_set(x_50, 6, x_40);
lean_ctor_set(x_50, 7, x_45);
lean_ctor_set(x_50, 8, x_46);
lean_ctor_set(x_50, 9, x_47);
lean_ctor_set(x_50, 10, x_16);
lean_ctor_set(x_50, 11, x_48);
lean_ctor_set(x_50, 12, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*13, x_39);
lean_ctor_set_uint8(x_50, sizeof(void*)*13 + 1, x_41);
lean_ctor_set_uint8(x_50, sizeof(void*)*13 + 2, x_42);
lean_ctor_set_uint8(x_50, sizeof(void*)*13 + 3, x_43);
lean_ctor_set_uint8(x_50, sizeof(void*)*13 + 4, x_44);
x_51 = l_Lean_Meta_Grind_setENode(x_33, x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
x_54 = lean_box(0);
lean_ctor_set(x_51, 0, x_54);
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_16);
x_58 = !lean_is_exclusive(x_30);
if (x_58 == 0)
{
return x_30;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_30, 0);
x_60 = lean_ctor_get(x_30, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_30);
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
lean_dec(x_16);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_24);
lean_ctor_set(x_62, 1, x_25);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_11);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_1);
x_64 = lean_ctor_get(x_16, 0);
lean_inc(x_64);
lean_dec(x_16);
x_65 = lean_ctor_get(x_23, 0);
lean_inc(x_65);
lean_dec(x_23);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_11);
return x_67;
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_checkOffsetEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_checkOffsetEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_process_new_offset_eq(x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_process_new_offset_eq_lit(x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
default: 
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_checkCutsatEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_2, 11);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 11);
lean_inc(x_13);
lean_dec(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
lean_inc(x_18);
x_19 = l_Lean_Meta_Grind_isNum(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_17);
x_20 = l_Lean_Meta_Grind_getParents___redArg(x_18, x_3, x_11);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set_tag(x_13, 3);
lean_ctor_set(x_13, 0, x_22);
lean_ctor_set(x_20, 0, x_13);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set_tag(x_13, 3);
lean_ctor_set(x_13, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_13);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_18);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_11);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_13, 0);
lean_inc(x_28);
lean_dec(x_13);
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
lean_dec(x_2);
lean_inc(x_29);
x_30 = l_Lean_Meta_Grind_isNum(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_28);
x_31 = l_Lean_Meta_Grind_getParents___redArg(x_29, x_3, x_11);
lean_dec(x_29);
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
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_32);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_29);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_11);
return x_38;
}
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_2);
x_39 = lean_ctor_get(x_1, 11);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_12, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
lean_dec(x_1);
lean_inc(x_41);
x_42 = l_Lean_Meta_Grind_isNum(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_40);
x_43 = lean_st_ref_get(x_3, x_11);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Meta_Grind_Goal_getENode(x_44, x_41, x_9, x_10, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_47, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_47, 4);
lean_inc(x_53);
x_54 = lean_ctor_get(x_47, 5);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_47, sizeof(void*)*13);
x_56 = lean_ctor_get(x_47, 6);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_47, sizeof(void*)*13 + 1);
x_58 = lean_ctor_get_uint8(x_47, sizeof(void*)*13 + 2);
x_59 = lean_ctor_get_uint8(x_47, sizeof(void*)*13 + 3);
x_60 = lean_ctor_get_uint8(x_47, sizeof(void*)*13 + 4);
x_61 = lean_ctor_get(x_47, 7);
lean_inc(x_61);
x_62 = lean_ctor_get(x_47, 8);
lean_inc(x_62);
x_63 = lean_ctor_get(x_47, 9);
lean_inc(x_63);
x_64 = lean_ctor_get(x_47, 10);
lean_inc(x_64);
x_65 = lean_ctor_get(x_47, 12);
lean_inc(x_65);
lean_dec(x_47);
lean_inc(x_49);
x_66 = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(x_66, 0, x_49);
lean_ctor_set(x_66, 1, x_50);
lean_ctor_set(x_66, 2, x_51);
lean_ctor_set(x_66, 3, x_52);
lean_ctor_set(x_66, 4, x_53);
lean_ctor_set(x_66, 5, x_54);
lean_ctor_set(x_66, 6, x_56);
lean_ctor_set(x_66, 7, x_61);
lean_ctor_set(x_66, 8, x_62);
lean_ctor_set(x_66, 9, x_63);
lean_ctor_set(x_66, 10, x_64);
lean_ctor_set(x_66, 11, x_12);
lean_ctor_set(x_66, 12, x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*13, x_55);
lean_ctor_set_uint8(x_66, sizeof(void*)*13 + 1, x_57);
lean_ctor_set_uint8(x_66, sizeof(void*)*13 + 2, x_58);
lean_ctor_set_uint8(x_66, sizeof(void*)*13 + 3, x_59);
lean_ctor_set_uint8(x_66, sizeof(void*)*13 + 4, x_60);
lean_inc(x_49);
x_67 = l_Lean_Meta_Grind_setENode(x_49, x_66, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_48);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l_Lean_Meta_Grind_getParents___redArg(x_49, x_3, x_68);
lean_dec(x_49);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_69, 0, x_72);
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_69, 0);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_69);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_73);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_12);
x_77 = !lean_is_exclusive(x_46);
if (x_77 == 0)
{
return x_46;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_46, 0);
x_79 = lean_ctor_get(x_46, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_46);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_12);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_40);
lean_ctor_set(x_81, 1, x_41);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_11);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_1);
x_83 = lean_ctor_get(x_12, 0);
lean_inc(x_83);
lean_dec(x_12);
x_84 = lean_ctor_get(x_39, 0);
lean_inc(x_84);
lean_dec(x_39);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_11);
return x_86;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_checkCutsatEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_checkCutsatEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCutsat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_process_cutsat_eq(x_13, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
case 2:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_process_cutsat_eq_lit(x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = l_Lean_Meta_Grind_propagateCutsatDiseqs(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_checkCommRingEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_2, 12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 12);
lean_inc(x_13);
lean_dec(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_2, 0);
x_19 = l_Lean_Meta_Grind_getParents___redArg(x_18, x_3, x_11);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set_tag(x_13, 3);
lean_ctor_set(x_13, 0, x_21);
lean_ctor_set(x_19, 0, x_13);
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
lean_ctor_set_tag(x_13, 3);
lean_ctor_set(x_13, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_13);
x_25 = lean_ctor_get(x_2, 0);
x_26 = l_Lean_Meta_Grind_getParents___redArg(x_25, x_3, x_11);
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
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_27);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_1, 12);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_st_ref_get(x_3, x_11);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = l_Lean_Meta_Grind_Goal_getENode(x_34, x_36, x_9, x_10, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_38, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_38, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 5);
lean_inc(x_45);
x_46 = lean_ctor_get_uint8(x_38, sizeof(void*)*13);
x_47 = lean_ctor_get(x_38, 6);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_38, sizeof(void*)*13 + 1);
x_49 = lean_ctor_get_uint8(x_38, sizeof(void*)*13 + 2);
x_50 = lean_ctor_get_uint8(x_38, sizeof(void*)*13 + 3);
x_51 = lean_ctor_get_uint8(x_38, sizeof(void*)*13 + 4);
x_52 = lean_ctor_get(x_38, 7);
lean_inc(x_52);
x_53 = lean_ctor_get(x_38, 8);
lean_inc(x_53);
x_54 = lean_ctor_get(x_38, 9);
lean_inc(x_54);
x_55 = lean_ctor_get(x_38, 10);
lean_inc(x_55);
x_56 = lean_ctor_get(x_38, 11);
lean_inc(x_56);
lean_dec(x_38);
lean_inc(x_12);
lean_inc(x_40);
x_57 = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(x_57, 0, x_40);
lean_ctor_set(x_57, 1, x_41);
lean_ctor_set(x_57, 2, x_42);
lean_ctor_set(x_57, 3, x_43);
lean_ctor_set(x_57, 4, x_44);
lean_ctor_set(x_57, 5, x_45);
lean_ctor_set(x_57, 6, x_47);
lean_ctor_set(x_57, 7, x_52);
lean_ctor_set(x_57, 8, x_53);
lean_ctor_set(x_57, 9, x_54);
lean_ctor_set(x_57, 10, x_55);
lean_ctor_set(x_57, 11, x_56);
lean_ctor_set(x_57, 12, x_12);
lean_ctor_set_uint8(x_57, sizeof(void*)*13, x_46);
lean_ctor_set_uint8(x_57, sizeof(void*)*13 + 1, x_48);
lean_ctor_set_uint8(x_57, sizeof(void*)*13 + 2, x_49);
lean_ctor_set_uint8(x_57, sizeof(void*)*13 + 3, x_50);
lean_ctor_set_uint8(x_57, sizeof(void*)*13 + 4, x_51);
lean_inc(x_40);
x_58 = l_Lean_Meta_Grind_setENode(x_40, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lean_Meta_Grind_getParents___redArg(x_40, x_3, x_59);
lean_dec(x_40);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_60, 0, x_63);
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_60, 0);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_60);
x_66 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_66, 0, x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_37);
if (x_68 == 0)
{
return x_37;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_37, 0);
x_70 = lean_ctor_get(x_37, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_37);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_1);
x_72 = lean_ctor_get(x_12, 0);
x_73 = lean_ctor_get(x_32, 0);
lean_inc(x_73);
lean_dec(x_32);
lean_inc(x_72);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_11);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_checkCommRingEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_checkCommRingEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCommRing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_process_ring_eq(x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
case 3:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Meta_Grind_propagateCommRingDiseqs(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
default: 
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_propagateBeta_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_79 = lean_mk_string_unchecked("grind", 5, 5);
x_80 = lean_mk_string_unchecked("debug", 5, 5);
x_81 = lean_mk_string_unchecked("beta", 4, 4);
x_82 = l_Lean_Name_mkStr3(x_79, x_80, x_81);
lean_inc(x_82);
x_83 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_82, x_11, x_13);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_82);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_ctor_get(x_4, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_4, 1);
lean_inc(x_88);
lean_dec(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_55 = x_87;
x_56 = x_88;
x_57 = x_5;
x_58 = x_6;
x_59 = x_7;
x_60 = x_8;
x_61 = x_9;
x_62 = x_10;
x_63 = x_11;
x_64 = x_12;
x_65 = x_86;
goto block_78;
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_83);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_83, 1);
x_91 = lean_ctor_get(x_83, 0);
lean_dec(x_91);
x_92 = lean_ctor_get(x_4, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_4, 1);
lean_inc(x_93);
lean_dec(x_4);
x_94 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_90);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_mk_string_unchecked("curr: ", 6, 6);
x_97 = l_Lean_stringToMessageData(x_96);
lean_dec(x_96);
lean_inc(x_93);
x_98 = l_Lean_MessageData_ofExpr(x_93);
lean_ctor_set_tag(x_83, 7);
lean_ctor_set(x_83, 1, x_98);
lean_ctor_set(x_83, 0, x_97);
x_99 = lean_mk_string_unchecked("", 0, 0);
x_100 = l_Lean_stringToMessageData(x_99);
lean_dec(x_99);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_83);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_82, x_101, x_9, x_10, x_11, x_12, x_95);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_55 = x_92;
x_56 = x_93;
x_57 = x_5;
x_58 = x_6;
x_59 = x_7;
x_60 = x_8;
x_61 = x_9;
x_62 = x_10;
x_63 = x_11;
x_64 = x_12;
x_65 = x_103;
goto block_78;
}
else
{
uint8_t x_104; 
lean_dec(x_93);
lean_dec(x_92);
lean_free_object(x_83);
lean_dec(x_82);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_104 = !lean_is_exclusive(x_94);
if (x_104 == 0)
{
return x_94;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_94, 0);
x_106 = lean_ctor_get(x_94, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_94);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_83, 1);
lean_inc(x_108);
lean_dec(x_83);
x_109 = lean_ctor_get(x_4, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_4, 1);
lean_inc(x_110);
lean_dec(x_4);
x_111 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_108);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_mk_string_unchecked("curr: ", 6, 6);
x_114 = l_Lean_stringToMessageData(x_113);
lean_dec(x_113);
lean_inc(x_110);
x_115 = l_Lean_MessageData_ofExpr(x_110);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_mk_string_unchecked("", 0, 0);
x_118 = l_Lean_stringToMessageData(x_117);
lean_dec(x_117);
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_82, x_119, x_9, x_10, x_11, x_12, x_112);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_55 = x_109;
x_56 = x_110;
x_57 = x_5;
x_58 = x_6;
x_59 = x_7;
x_60 = x_8;
x_61 = x_9;
x_62 = x_10;
x_63 = x_11;
x_64 = x_12;
x_65 = x_121;
goto block_78;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_82);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_122 = lean_ctor_get(x_111, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_111, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_124 = x_111;
} else {
 lean_dec_ref(x_111);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
}
block_54:
{
if (lean_obj_tag(x_15) == 5)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
x_27 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_16, x_24);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_box(0);
x_32 = lean_grind_internalize(x_15, x_29, x_31, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_array_push(x_14, x_26);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 0, x_34);
x_4 = x_27;
x_13 = x_33;
goto _start;
}
else
{
uint8_t x_36; 
lean_free_object(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_27, 0);
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_27);
x_42 = lean_box(0);
x_43 = lean_grind_internalize(x_15, x_40, x_42, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_array_push(x_14, x_26);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_25);
x_4 = x_46;
x_13 = x_44;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_50 = x_43;
} else {
 lean_dec_ref(x_43);
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
lean_object* x_52; lean_object* x_53; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_14);
lean_ctor_set(x_52, 1, x_15);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_24);
return x_53;
}
}
block_78:
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = l_Lean_Meta_Grind_isEqv___redArg(x_56, x_2, x_57, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_14 = x_55;
x_15 = x_56;
x_16 = x_57;
x_17 = x_58;
x_18 = x_59;
x_19 = x_60;
x_20 = x_61;
x_21 = x_62;
x_22 = x_63;
x_23 = x_64;
x_24 = x_69;
goto block_54;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec(x_66);
lean_inc(x_55);
x_71 = l_Array_reverse(lean_box(0), x_55);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
x_72 = l_Lean_Meta_Grind_propagateBetaEqs(x_3, x_56, x_71, x_57, x_58, x_59, x_60, x_61, x_62, x_63, x_64, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_14 = x_55;
x_15 = x_56;
x_16 = x_57;
x_17 = x_58;
x_18 = x_59;
x_19 = x_60;
x_20 = x_61;
x_21 = x_62;
x_22 = x_63;
x_23 = x_64;
x_24 = x_73;
goto block_54;
}
else
{
uint8_t x_74; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
return x_72;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_72, 0);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_72);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_propagateBeta_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_79 = lean_mk_string_unchecked("grind", 5, 5);
x_80 = lean_mk_string_unchecked("debug", 5, 5);
x_81 = lean_mk_string_unchecked("beta", 4, 4);
x_82 = l_Lean_Name_mkStr3(x_79, x_80, x_81);
lean_inc(x_82);
x_83 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_82, x_11, x_13);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_82);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_ctor_get(x_4, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_4, 1);
lean_inc(x_88);
lean_dec(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_55 = x_87;
x_56 = x_88;
x_57 = x_5;
x_58 = x_6;
x_59 = x_7;
x_60 = x_8;
x_61 = x_9;
x_62 = x_10;
x_63 = x_11;
x_64 = x_12;
x_65 = x_86;
goto block_78;
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_83);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_83, 1);
x_91 = lean_ctor_get(x_83, 0);
lean_dec(x_91);
x_92 = lean_ctor_get(x_4, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_4, 1);
lean_inc(x_93);
lean_dec(x_4);
x_94 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_90);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_mk_string_unchecked("curr: ", 6, 6);
x_97 = l_Lean_stringToMessageData(x_96);
lean_dec(x_96);
lean_inc(x_93);
x_98 = l_Lean_MessageData_ofExpr(x_93);
lean_ctor_set_tag(x_83, 7);
lean_ctor_set(x_83, 1, x_98);
lean_ctor_set(x_83, 0, x_97);
x_99 = lean_mk_string_unchecked("", 0, 0);
x_100 = l_Lean_stringToMessageData(x_99);
lean_dec(x_99);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_83);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_82, x_101, x_9, x_10, x_11, x_12, x_95);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_55 = x_92;
x_56 = x_93;
x_57 = x_5;
x_58 = x_6;
x_59 = x_7;
x_60 = x_8;
x_61 = x_9;
x_62 = x_10;
x_63 = x_11;
x_64 = x_12;
x_65 = x_103;
goto block_78;
}
else
{
uint8_t x_104; 
lean_dec(x_93);
lean_dec(x_92);
lean_free_object(x_83);
lean_dec(x_82);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_104 = !lean_is_exclusive(x_94);
if (x_104 == 0)
{
return x_94;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_94, 0);
x_106 = lean_ctor_get(x_94, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_94);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_83, 1);
lean_inc(x_108);
lean_dec(x_83);
x_109 = lean_ctor_get(x_4, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_4, 1);
lean_inc(x_110);
lean_dec(x_4);
x_111 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_108);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_mk_string_unchecked("curr: ", 6, 6);
x_114 = l_Lean_stringToMessageData(x_113);
lean_dec(x_113);
lean_inc(x_110);
x_115 = l_Lean_MessageData_ofExpr(x_110);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_mk_string_unchecked("", 0, 0);
x_118 = l_Lean_stringToMessageData(x_117);
lean_dec(x_117);
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_82, x_119, x_9, x_10, x_11, x_12, x_112);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_55 = x_109;
x_56 = x_110;
x_57 = x_5;
x_58 = x_6;
x_59 = x_7;
x_60 = x_8;
x_61 = x_9;
x_62 = x_10;
x_63 = x_11;
x_64 = x_12;
x_65 = x_121;
goto block_78;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_82);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_122 = lean_ctor_get(x_111, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_111, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_124 = x_111;
} else {
 lean_dec_ref(x_111);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
}
block_54:
{
if (lean_obj_tag(x_15) == 5)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
x_27 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_16, x_24);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_box(0);
x_32 = lean_grind_internalize(x_15, x_29, x_31, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_array_push(x_14, x_26);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 0, x_34);
x_35 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_propagateBeta_spec__0_spec__0(x_1, x_2, x_3, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_33);
return x_35;
}
else
{
uint8_t x_36; 
lean_free_object(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_27, 0);
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_27);
x_42 = lean_box(0);
x_43 = lean_grind_internalize(x_15, x_40, x_42, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_array_push(x_14, x_26);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_25);
x_47 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_propagateBeta_spec__0_spec__0(x_1, x_2, x_3, x_46, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_44);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_50 = x_43;
} else {
 lean_dec_ref(x_43);
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
lean_object* x_52; lean_object* x_53; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_14);
lean_ctor_set(x_52, 1, x_15);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_24);
return x_53;
}
}
block_78:
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = l_Lean_Meta_Grind_isEqv___redArg(x_56, x_2, x_57, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_14 = x_55;
x_15 = x_56;
x_16 = x_57;
x_17 = x_58;
x_18 = x_59;
x_19 = x_60;
x_20 = x_61;
x_21 = x_62;
x_22 = x_63;
x_23 = x_64;
x_24 = x_69;
goto block_54;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec(x_66);
lean_inc(x_55);
x_71 = l_Array_reverse(lean_box(0), x_55);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
x_72 = l_Lean_Meta_Grind_propagateBetaEqs(x_3, x_56, x_71, x_57, x_58, x_59, x_60, x_61, x_62, x_63, x_64, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_14 = x_55;
x_15 = x_56;
x_16 = x_57;
x_17 = x_58;
x_18 = x_59;
x_19 = x_60;
x_20 = x_61;
x_21 = x_62;
x_22 = x_63;
x_23 = x_64;
x_24 = x_73;
goto block_54;
}
else
{
uint8_t x_74; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
return x_72;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_72, 0);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_72);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_Grind_propagateBeta_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 4);
lean_inc(x_16);
lean_dec(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_Grind_propagateBeta_spec__2_spec__2(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
else
{
uint8_t x_19; 
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_mk_string_unchecked("grind", 5, 5);
x_23 = lean_mk_string_unchecked("debug", 5, 5);
x_24 = lean_mk_string_unchecked("beta", 4, 4);
x_25 = l_Lean_Name_mkStr3(x_22, x_23, x_24);
lean_inc(x_25);
x_26 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_25, x_11, x_20);
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
x_30 = lean_box(0);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_mk_empty_array_with_capacity(x_51);
x_53 = lean_unbox(x_27);
lean_dec(x_27);
if (x_53 == 0)
{
lean_dec(x_25);
lean_free_object(x_17);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_31 = x_52;
x_32 = x_14;
x_33 = x_5;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = x_28;
goto block_50;
}
else
{
lean_object* x_54; 
x_54 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_28);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_mk_string_unchecked("parent: ", 8, 8);
x_57 = l_Lean_stringToMessageData(x_56);
lean_dec(x_56);
lean_inc(x_14);
x_58 = l_Lean_MessageData_ofExpr(x_14);
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_58);
lean_ctor_set(x_17, 0, x_57);
x_59 = lean_mk_string_unchecked("", 0, 0);
x_60 = l_Lean_stringToMessageData(x_59);
lean_dec(x_59);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_17);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_25, x_61, x_9, x_10, x_11, x_12, x_55);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_31 = x_52;
x_32 = x_14;
x_33 = x_5;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = x_63;
goto block_50;
}
else
{
uint8_t x_64; 
lean_dec(x_52);
lean_dec(x_29);
lean_dec(x_25);
lean_free_object(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_64 = !lean_is_exclusive(x_54);
if (x_64 == 0)
{
return x_54;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_54, 0);
x_66 = lean_ctor_get(x_54, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_54);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
block_50:
{
lean_object* x_42; lean_object* x_43; 
if (lean_is_scalar(x_29)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_29;
}
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_32);
x_43 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_propagateBeta_spec__0(x_14, x_1, x_2, x_42, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40, x_41);
lean_dec(x_14);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_3 = x_30;
x_4 = x_16;
x_13 = x_44;
goto _start;
}
else
{
uint8_t x_46; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
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
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_68 = lean_ctor_get(x_17, 1);
lean_inc(x_68);
lean_dec(x_17);
x_69 = lean_mk_string_unchecked("grind", 5, 5);
x_70 = lean_mk_string_unchecked("debug", 5, 5);
x_71 = lean_mk_string_unchecked("beta", 4, 4);
x_72 = l_Lean_Name_mkStr3(x_69, x_70, x_71);
lean_inc(x_72);
x_73 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_72, x_11, x_68);
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
x_77 = lean_box(0);
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_mk_empty_array_with_capacity(x_98);
x_100 = lean_unbox(x_74);
lean_dec(x_74);
if (x_100 == 0)
{
lean_dec(x_72);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_78 = x_99;
x_79 = x_14;
x_80 = x_5;
x_81 = x_6;
x_82 = x_7;
x_83 = x_8;
x_84 = x_9;
x_85 = x_10;
x_86 = x_11;
x_87 = x_12;
x_88 = x_75;
goto block_97;
}
else
{
lean_object* x_101; 
x_101 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_75);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_mk_string_unchecked("parent: ", 8, 8);
x_104 = l_Lean_stringToMessageData(x_103);
lean_dec(x_103);
lean_inc(x_14);
x_105 = l_Lean_MessageData_ofExpr(x_14);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_mk_string_unchecked("", 0, 0);
x_108 = l_Lean_stringToMessageData(x_107);
lean_dec(x_107);
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_72, x_109, x_9, x_10, x_11, x_12, x_102);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_78 = x_99;
x_79 = x_14;
x_80 = x_5;
x_81 = x_6;
x_82 = x_7;
x_83 = x_8;
x_84 = x_9;
x_85 = x_10;
x_86 = x_11;
x_87 = x_12;
x_88 = x_111;
goto block_97;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_99);
lean_dec(x_76);
lean_dec(x_72);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_112 = lean_ctor_get(x_101, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_101, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_114 = x_101;
} else {
 lean_dec_ref(x_101);
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
block_97:
{
lean_object* x_89; lean_object* x_90; 
if (lean_is_scalar(x_76)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_76;
}
lean_ctor_set(x_89, 0, x_78);
lean_ctor_set(x_89, 1, x_79);
x_90 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_propagateBeta_spec__0(x_14, x_1, x_2, x_89, x_80, x_81, x_82, x_83, x_84, x_85, x_86, x_87, x_88);
lean_dec(x_14);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_3 = x_77;
x_4 = x_16;
x_13 = x_91;
goto _start;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_3);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_13);
return x_117;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_Grind_propagateBeta_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 4);
lean_inc(x_16);
lean_dec(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_Grind_propagateBeta_spec__2_spec__2(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
else
{
uint8_t x_19; 
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_mk_string_unchecked("grind", 5, 5);
x_23 = lean_mk_string_unchecked("debug", 5, 5);
x_24 = lean_mk_string_unchecked("beta", 4, 4);
x_25 = l_Lean_Name_mkStr3(x_22, x_23, x_24);
lean_inc(x_25);
x_26 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_25, x_11, x_20);
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
x_30 = lean_box(0);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_mk_empty_array_with_capacity(x_51);
x_53 = lean_unbox(x_27);
lean_dec(x_27);
if (x_53 == 0)
{
lean_dec(x_25);
lean_free_object(x_17);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_31 = x_52;
x_32 = x_14;
x_33 = x_5;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = x_28;
goto block_50;
}
else
{
lean_object* x_54; 
x_54 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_28);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_mk_string_unchecked("parent: ", 8, 8);
x_57 = l_Lean_stringToMessageData(x_56);
lean_dec(x_56);
lean_inc(x_14);
x_58 = l_Lean_MessageData_ofExpr(x_14);
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_58);
lean_ctor_set(x_17, 0, x_57);
x_59 = lean_mk_string_unchecked("", 0, 0);
x_60 = l_Lean_stringToMessageData(x_59);
lean_dec(x_59);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_17);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_25, x_61, x_9, x_10, x_11, x_12, x_55);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_31 = x_52;
x_32 = x_14;
x_33 = x_5;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = x_63;
goto block_50;
}
else
{
uint8_t x_64; 
lean_dec(x_52);
lean_dec(x_29);
lean_dec(x_25);
lean_free_object(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_64 = !lean_is_exclusive(x_54);
if (x_64 == 0)
{
return x_54;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_54, 0);
x_66 = lean_ctor_get(x_54, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_54);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
block_50:
{
lean_object* x_42; lean_object* x_43; 
if (lean_is_scalar(x_29)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_29;
}
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_32);
x_43 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_propagateBeta_spec__0(x_14, x_1, x_2, x_42, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40, x_41);
lean_dec(x_14);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_Grind_propagateBeta_spec__2_spec__2(x_1, x_2, x_30, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_44);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
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
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_68 = lean_ctor_get(x_17, 1);
lean_inc(x_68);
lean_dec(x_17);
x_69 = lean_mk_string_unchecked("grind", 5, 5);
x_70 = lean_mk_string_unchecked("debug", 5, 5);
x_71 = lean_mk_string_unchecked("beta", 4, 4);
x_72 = l_Lean_Name_mkStr3(x_69, x_70, x_71);
lean_inc(x_72);
x_73 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_72, x_11, x_68);
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
x_77 = lean_box(0);
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_mk_empty_array_with_capacity(x_98);
x_100 = lean_unbox(x_74);
lean_dec(x_74);
if (x_100 == 0)
{
lean_dec(x_72);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_78 = x_99;
x_79 = x_14;
x_80 = x_5;
x_81 = x_6;
x_82 = x_7;
x_83 = x_8;
x_84 = x_9;
x_85 = x_10;
x_86 = x_11;
x_87 = x_12;
x_88 = x_75;
goto block_97;
}
else
{
lean_object* x_101; 
x_101 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_75);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_mk_string_unchecked("parent: ", 8, 8);
x_104 = l_Lean_stringToMessageData(x_103);
lean_dec(x_103);
lean_inc(x_14);
x_105 = l_Lean_MessageData_ofExpr(x_14);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_mk_string_unchecked("", 0, 0);
x_108 = l_Lean_stringToMessageData(x_107);
lean_dec(x_107);
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_72, x_109, x_9, x_10, x_11, x_12, x_102);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_78 = x_99;
x_79 = x_14;
x_80 = x_5;
x_81 = x_6;
x_82 = x_7;
x_83 = x_8;
x_84 = x_9;
x_85 = x_10;
x_86 = x_11;
x_87 = x_12;
x_88 = x_111;
goto block_97;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_99);
lean_dec(x_76);
lean_dec(x_72);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_112 = lean_ctor_get(x_101, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_101, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_114 = x_101;
} else {
 lean_dec_ref(x_101);
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
block_97:
{
lean_object* x_89; lean_object* x_90; 
if (lean_is_scalar(x_76)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_76;
}
lean_ctor_set(x_89, 0, x_78);
lean_ctor_set(x_89, 1, x_79);
x_90 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_propagateBeta_spec__0(x_14, x_1, x_2, x_89, x_80, x_81, x_82, x_83, x_84, x_85, x_86, x_87, x_88);
lean_dec(x_14);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_Grind_propagateBeta_spec__2_spec__2(x_1, x_2, x_77, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_3);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_13);
return x_117;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_Grind_propagateBeta_spec__4_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 4);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_Grind_propagateBeta_spec__4_spec__4(x_1, x_4);
x_7 = lean_array_push(x_6, x_3);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_Grind_propagateBeta_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_Grind_propagateBeta_spec__4_spec__4(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_propagateBeta_spec__6_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_23; 
x_23 = lean_usize_dec_lt(x_5, x_4);
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
lean_dec(x_7);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_15);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_6);
x_25 = lean_mk_string_unchecked("grind", 5, 5);
x_26 = lean_mk_string_unchecked("debug", 5, 5);
x_27 = lean_mk_string_unchecked("beta", 4, 4);
x_28 = l_Lean_Name_mkStr3(x_25, x_26, x_27);
lean_inc(x_28);
x_29 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_28, x_13, x_15);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_63; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_box(0);
x_34 = lean_array_uget(x_3, x_5);
x_63 = lean_unbox(x_31);
lean_dec(x_31);
if (x_63 == 0)
{
lean_free_object(x_29);
lean_dec(x_28);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = x_13;
x_42 = x_14;
x_43 = x_32;
goto block_62;
}
else
{
lean_object* x_64; 
x_64 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_32);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_64, 1);
x_67 = lean_ctor_get(x_64, 0);
lean_dec(x_67);
x_68 = l_Lean_Meta_Grind_getParents___redArg(x_34, x_7, x_66);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_ctor_get(x_68, 1);
x_72 = lean_mk_string_unchecked("fn: ", 4, 4);
x_73 = l_Lean_stringToMessageData(x_72);
lean_dec(x_72);
lean_inc(x_34);
x_74 = l_Lean_MessageData_ofExpr(x_34);
lean_ctor_set_tag(x_68, 7);
lean_ctor_set(x_68, 1, x_74);
lean_ctor_set(x_68, 0, x_73);
x_75 = lean_mk_string_unchecked(", parents: ", 11, 11);
x_76 = l_Lean_stringToMessageData(x_75);
lean_dec(x_75);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_76);
lean_ctor_set(x_64, 0, x_68);
x_77 = l_Array_empty(lean_box(0));
x_78 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_Grind_propagateBeta_spec__4_spec__4(x_77, x_70);
x_79 = lean_array_to_list(x_78);
x_80 = lean_box(0);
x_81 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_79, x_80);
x_82 = l_Lean_MessageData_ofList(x_81);
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_82);
lean_ctor_set(x_29, 0, x_64);
x_83 = lean_mk_string_unchecked("", 0, 0);
x_84 = l_Lean_stringToMessageData(x_83);
lean_dec(x_83);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_29);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_28, x_85, x_11, x_12, x_13, x_14, x_71);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = x_13;
x_42 = x_14;
x_43 = x_87;
goto block_62;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_88 = lean_ctor_get(x_68, 0);
x_89 = lean_ctor_get(x_68, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_68);
x_90 = lean_mk_string_unchecked("fn: ", 4, 4);
x_91 = l_Lean_stringToMessageData(x_90);
lean_dec(x_90);
lean_inc(x_34);
x_92 = l_Lean_MessageData_ofExpr(x_34);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_mk_string_unchecked(", parents: ", 11, 11);
x_95 = l_Lean_stringToMessageData(x_94);
lean_dec(x_94);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_95);
lean_ctor_set(x_64, 0, x_93);
x_96 = l_Array_empty(lean_box(0));
x_97 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_Grind_propagateBeta_spec__4_spec__4(x_96, x_88);
x_98 = lean_array_to_list(x_97);
x_99 = lean_box(0);
x_100 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_98, x_99);
x_101 = l_Lean_MessageData_ofList(x_100);
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_101);
lean_ctor_set(x_29, 0, x_64);
x_102 = lean_mk_string_unchecked("", 0, 0);
x_103 = l_Lean_stringToMessageData(x_102);
lean_dec(x_102);
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_29);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_28, x_104, x_11, x_12, x_13, x_14, x_89);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = x_13;
x_42 = x_14;
x_43 = x_106;
goto block_62;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_107 = lean_ctor_get(x_64, 1);
lean_inc(x_107);
lean_dec(x_64);
x_108 = l_Lean_Meta_Grind_getParents___redArg(x_34, x_7, x_107);
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
x_112 = lean_mk_string_unchecked("fn: ", 4, 4);
x_113 = l_Lean_stringToMessageData(x_112);
lean_dec(x_112);
lean_inc(x_34);
x_114 = l_Lean_MessageData_ofExpr(x_34);
if (lean_is_scalar(x_111)) {
 x_115 = lean_alloc_ctor(7, 2, 0);
} else {
 x_115 = x_111;
 lean_ctor_set_tag(x_115, 7);
}
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_mk_string_unchecked(", parents: ", 11, 11);
x_117 = l_Lean_stringToMessageData(x_116);
lean_dec(x_116);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Array_empty(lean_box(0));
x_120 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_Grind_propagateBeta_spec__4_spec__4(x_119, x_109);
x_121 = lean_array_to_list(x_120);
x_122 = lean_box(0);
x_123 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_121, x_122);
x_124 = l_Lean_MessageData_ofList(x_123);
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_124);
lean_ctor_set(x_29, 0, x_118);
x_125 = lean_mk_string_unchecked("", 0, 0);
x_126 = l_Lean_stringToMessageData(x_125);
lean_dec(x_125);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_29);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_28, x_127, x_11, x_12, x_13, x_14, x_110);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = x_13;
x_42 = x_14;
x_43 = x_129;
goto block_62;
}
}
else
{
lean_dec(x_34);
lean_free_object(x_29);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_64;
}
}
block_62:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = l_Lean_Meta_Grind_getParents___redArg(x_34, x_35, x_43);
lean_dec(x_34);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_Grind_propagateBeta_spec__2(x_1, x_2, x_33, x_45, x_35, x_36, x_37, x_38, x_39, x_40, x_41, x_42, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_16 = x_33;
x_17 = x_48;
goto block_22;
}
else
{
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_47, 0);
lean_dec(x_51);
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
lean_dec(x_49);
lean_ctor_set_tag(x_47, 0);
lean_ctor_set(x_47, 0, x_52);
return x_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_dec(x_47);
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
lean_dec(x_49);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_dec(x_47);
x_57 = lean_ctor_get(x_49, 0);
lean_inc(x_57);
lean_dec(x_49);
x_16 = x_57;
x_17 = x_56;
goto block_22;
}
}
else
{
uint8_t x_58; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_58 = !lean_is_exclusive(x_47);
if (x_58 == 0)
{
return x_47;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_47, 0);
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_47);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_160; 
x_130 = lean_ctor_get(x_29, 0);
x_131 = lean_ctor_get(x_29, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_29);
x_132 = lean_box(0);
x_133 = lean_array_uget(x_3, x_5);
x_160 = lean_unbox(x_130);
lean_dec(x_130);
if (x_160 == 0)
{
lean_dec(x_28);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_134 = x_7;
x_135 = x_8;
x_136 = x_9;
x_137 = x_10;
x_138 = x_11;
x_139 = x_12;
x_140 = x_13;
x_141 = x_14;
x_142 = x_131;
goto block_159;
}
else
{
lean_object* x_161; 
x_161 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_131);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_163 = x_161;
} else {
 lean_dec_ref(x_161);
 x_163 = lean_box(0);
}
x_164 = l_Lean_Meta_Grind_getParents___redArg(x_133, x_7, x_162);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_167 = x_164;
} else {
 lean_dec_ref(x_164);
 x_167 = lean_box(0);
}
x_168 = lean_mk_string_unchecked("fn: ", 4, 4);
x_169 = l_Lean_stringToMessageData(x_168);
lean_dec(x_168);
lean_inc(x_133);
x_170 = l_Lean_MessageData_ofExpr(x_133);
if (lean_is_scalar(x_167)) {
 x_171 = lean_alloc_ctor(7, 2, 0);
} else {
 x_171 = x_167;
 lean_ctor_set_tag(x_171, 7);
}
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_mk_string_unchecked(", parents: ", 11, 11);
x_173 = l_Lean_stringToMessageData(x_172);
lean_dec(x_172);
if (lean_is_scalar(x_163)) {
 x_174 = lean_alloc_ctor(7, 2, 0);
} else {
 x_174 = x_163;
 lean_ctor_set_tag(x_174, 7);
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_173);
x_175 = l_Array_empty(lean_box(0));
x_176 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_Grind_propagateBeta_spec__4_spec__4(x_175, x_165);
x_177 = lean_array_to_list(x_176);
x_178 = lean_box(0);
x_179 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_177, x_178);
x_180 = l_Lean_MessageData_ofList(x_179);
x_181 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_181, 0, x_174);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_mk_string_unchecked("", 0, 0);
x_183 = l_Lean_stringToMessageData(x_182);
lean_dec(x_182);
x_184 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_183);
x_185 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_28, x_184, x_11, x_12, x_13, x_14, x_166);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_134 = x_7;
x_135 = x_8;
x_136 = x_9;
x_137 = x_10;
x_138 = x_11;
x_139 = x_12;
x_140 = x_13;
x_141 = x_14;
x_142 = x_186;
goto block_159;
}
else
{
lean_dec(x_133);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_161;
}
}
block_159:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = l_Lean_Meta_Grind_getParents___redArg(x_133, x_134, x_142);
lean_dec(x_133);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_Grind_propagateBeta_spec__2(x_1, x_2, x_132, x_144, x_134, x_135, x_136, x_137, x_138, x_139, x_140, x_141, x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec(x_146);
x_16 = x_132;
x_17 = x_147;
goto block_22;
}
else
{
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_150 = x_146;
} else {
 lean_dec_ref(x_146);
 x_150 = lean_box(0);
}
x_151 = lean_ctor_get(x_148, 0);
lean_inc(x_151);
lean_dec(x_148);
if (lean_is_scalar(x_150)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_150;
 lean_ctor_set_tag(x_152, 0);
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_149);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_146, 1);
lean_inc(x_153);
lean_dec(x_146);
x_154 = lean_ctor_get(x_148, 0);
lean_inc(x_154);
lean_dec(x_148);
x_16 = x_154;
x_17 = x_153;
goto block_22;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_155 = lean_ctor_get(x_146, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_146, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_157 = x_146;
} else {
 lean_dec_ref(x_146);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
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
x_20 = lean_usize_add(x_5, x_19);
x_5 = x_20;
x_6 = x_16;
x_15 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_propagateBeta_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_23; 
x_23 = lean_usize_dec_lt(x_5, x_4);
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
lean_dec(x_7);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_15);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_6);
x_25 = lean_mk_string_unchecked("grind", 5, 5);
x_26 = lean_mk_string_unchecked("debug", 5, 5);
x_27 = lean_mk_string_unchecked("beta", 4, 4);
x_28 = l_Lean_Name_mkStr3(x_25, x_26, x_27);
lean_inc(x_28);
x_29 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_28, x_13, x_15);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_63; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_box(0);
x_34 = lean_array_uget(x_3, x_5);
x_63 = lean_unbox(x_31);
lean_dec(x_31);
if (x_63 == 0)
{
lean_free_object(x_29);
lean_dec(x_28);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = x_13;
x_42 = x_14;
x_43 = x_32;
goto block_62;
}
else
{
lean_object* x_64; 
x_64 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_32);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_64, 1);
x_67 = lean_ctor_get(x_64, 0);
lean_dec(x_67);
x_68 = l_Lean_Meta_Grind_getParents___redArg(x_34, x_7, x_66);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_ctor_get(x_68, 1);
x_72 = lean_mk_string_unchecked("fn: ", 4, 4);
x_73 = l_Lean_stringToMessageData(x_72);
lean_dec(x_72);
lean_inc(x_34);
x_74 = l_Lean_MessageData_ofExpr(x_34);
lean_ctor_set_tag(x_68, 7);
lean_ctor_set(x_68, 1, x_74);
lean_ctor_set(x_68, 0, x_73);
x_75 = lean_mk_string_unchecked(", parents: ", 11, 11);
x_76 = l_Lean_stringToMessageData(x_75);
lean_dec(x_75);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_76);
lean_ctor_set(x_64, 0, x_68);
x_77 = l_Array_empty(lean_box(0));
x_78 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_Grind_propagateBeta_spec__4_spec__4(x_77, x_70);
x_79 = lean_array_to_list(x_78);
x_80 = lean_box(0);
x_81 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_79, x_80);
x_82 = l_Lean_MessageData_ofList(x_81);
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_82);
lean_ctor_set(x_29, 0, x_64);
x_83 = lean_mk_string_unchecked("", 0, 0);
x_84 = l_Lean_stringToMessageData(x_83);
lean_dec(x_83);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_29);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_28, x_85, x_11, x_12, x_13, x_14, x_71);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = x_13;
x_42 = x_14;
x_43 = x_87;
goto block_62;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_88 = lean_ctor_get(x_68, 0);
x_89 = lean_ctor_get(x_68, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_68);
x_90 = lean_mk_string_unchecked("fn: ", 4, 4);
x_91 = l_Lean_stringToMessageData(x_90);
lean_dec(x_90);
lean_inc(x_34);
x_92 = l_Lean_MessageData_ofExpr(x_34);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_mk_string_unchecked(", parents: ", 11, 11);
x_95 = l_Lean_stringToMessageData(x_94);
lean_dec(x_94);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_95);
lean_ctor_set(x_64, 0, x_93);
x_96 = l_Array_empty(lean_box(0));
x_97 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_Grind_propagateBeta_spec__4_spec__4(x_96, x_88);
x_98 = lean_array_to_list(x_97);
x_99 = lean_box(0);
x_100 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_98, x_99);
x_101 = l_Lean_MessageData_ofList(x_100);
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_101);
lean_ctor_set(x_29, 0, x_64);
x_102 = lean_mk_string_unchecked("", 0, 0);
x_103 = l_Lean_stringToMessageData(x_102);
lean_dec(x_102);
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_29);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_28, x_104, x_11, x_12, x_13, x_14, x_89);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = x_13;
x_42 = x_14;
x_43 = x_106;
goto block_62;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_107 = lean_ctor_get(x_64, 1);
lean_inc(x_107);
lean_dec(x_64);
x_108 = l_Lean_Meta_Grind_getParents___redArg(x_34, x_7, x_107);
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
x_112 = lean_mk_string_unchecked("fn: ", 4, 4);
x_113 = l_Lean_stringToMessageData(x_112);
lean_dec(x_112);
lean_inc(x_34);
x_114 = l_Lean_MessageData_ofExpr(x_34);
if (lean_is_scalar(x_111)) {
 x_115 = lean_alloc_ctor(7, 2, 0);
} else {
 x_115 = x_111;
 lean_ctor_set_tag(x_115, 7);
}
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_mk_string_unchecked(", parents: ", 11, 11);
x_117 = l_Lean_stringToMessageData(x_116);
lean_dec(x_116);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Array_empty(lean_box(0));
x_120 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_Grind_propagateBeta_spec__4_spec__4(x_119, x_109);
x_121 = lean_array_to_list(x_120);
x_122 = lean_box(0);
x_123 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_121, x_122);
x_124 = l_Lean_MessageData_ofList(x_123);
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_124);
lean_ctor_set(x_29, 0, x_118);
x_125 = lean_mk_string_unchecked("", 0, 0);
x_126 = l_Lean_stringToMessageData(x_125);
lean_dec(x_125);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_29);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_28, x_127, x_11, x_12, x_13, x_14, x_110);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = x_13;
x_42 = x_14;
x_43 = x_129;
goto block_62;
}
}
else
{
lean_dec(x_34);
lean_free_object(x_29);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_64;
}
}
block_62:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = l_Lean_Meta_Grind_getParents___redArg(x_34, x_35, x_43);
lean_dec(x_34);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_Grind_propagateBeta_spec__2(x_1, x_2, x_33, x_45, x_35, x_36, x_37, x_38, x_39, x_40, x_41, x_42, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_16 = x_33;
x_17 = x_48;
goto block_22;
}
else
{
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_47, 0);
lean_dec(x_51);
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
lean_dec(x_49);
lean_ctor_set_tag(x_47, 0);
lean_ctor_set(x_47, 0, x_52);
return x_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_dec(x_47);
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
lean_dec(x_49);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_dec(x_47);
x_57 = lean_ctor_get(x_49, 0);
lean_inc(x_57);
lean_dec(x_49);
x_16 = x_57;
x_17 = x_56;
goto block_22;
}
}
else
{
uint8_t x_58; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_58 = !lean_is_exclusive(x_47);
if (x_58 == 0)
{
return x_47;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_47, 0);
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_47);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_160; 
x_130 = lean_ctor_get(x_29, 0);
x_131 = lean_ctor_get(x_29, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_29);
x_132 = lean_box(0);
x_133 = lean_array_uget(x_3, x_5);
x_160 = lean_unbox(x_130);
lean_dec(x_130);
if (x_160 == 0)
{
lean_dec(x_28);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_134 = x_7;
x_135 = x_8;
x_136 = x_9;
x_137 = x_10;
x_138 = x_11;
x_139 = x_12;
x_140 = x_13;
x_141 = x_14;
x_142 = x_131;
goto block_159;
}
else
{
lean_object* x_161; 
x_161 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_131);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_163 = x_161;
} else {
 lean_dec_ref(x_161);
 x_163 = lean_box(0);
}
x_164 = l_Lean_Meta_Grind_getParents___redArg(x_133, x_7, x_162);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_167 = x_164;
} else {
 lean_dec_ref(x_164);
 x_167 = lean_box(0);
}
x_168 = lean_mk_string_unchecked("fn: ", 4, 4);
x_169 = l_Lean_stringToMessageData(x_168);
lean_dec(x_168);
lean_inc(x_133);
x_170 = l_Lean_MessageData_ofExpr(x_133);
if (lean_is_scalar(x_167)) {
 x_171 = lean_alloc_ctor(7, 2, 0);
} else {
 x_171 = x_167;
 lean_ctor_set_tag(x_171, 7);
}
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_mk_string_unchecked(", parents: ", 11, 11);
x_173 = l_Lean_stringToMessageData(x_172);
lean_dec(x_172);
if (lean_is_scalar(x_163)) {
 x_174 = lean_alloc_ctor(7, 2, 0);
} else {
 x_174 = x_163;
 lean_ctor_set_tag(x_174, 7);
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_173);
x_175 = l_Array_empty(lean_box(0));
x_176 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Meta_Grind_propagateBeta_spec__4_spec__4(x_175, x_165);
x_177 = lean_array_to_list(x_176);
x_178 = lean_box(0);
x_179 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_177, x_178);
x_180 = l_Lean_MessageData_ofList(x_179);
x_181 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_181, 0, x_174);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_mk_string_unchecked("", 0, 0);
x_183 = l_Lean_stringToMessageData(x_182);
lean_dec(x_182);
x_184 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_183);
x_185 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_28, x_184, x_11, x_12, x_13, x_14, x_166);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_134 = x_7;
x_135 = x_8;
x_136 = x_9;
x_137 = x_10;
x_138 = x_11;
x_139 = x_12;
x_140 = x_13;
x_141 = x_14;
x_142 = x_186;
goto block_159;
}
else
{
lean_dec(x_133);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_161;
}
}
block_159:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = l_Lean_Meta_Grind_getParents___redArg(x_133, x_134, x_142);
lean_dec(x_133);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_Grind_propagateBeta_spec__2(x_1, x_2, x_132, x_144, x_134, x_135, x_136, x_137, x_138, x_139, x_140, x_141, x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec(x_146);
x_16 = x_132;
x_17 = x_147;
goto block_22;
}
else
{
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_150 = x_146;
} else {
 lean_dec_ref(x_146);
 x_150 = lean_box(0);
}
x_151 = lean_ctor_get(x_148, 0);
lean_inc(x_151);
lean_dec(x_148);
if (lean_is_scalar(x_150)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_150;
 lean_ctor_set_tag(x_152, 0);
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_149);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_146, 1);
lean_inc(x_153);
lean_dec(x_146);
x_154 = lean_ctor_get(x_148, 0);
lean_inc(x_154);
lean_dec(x_148);
x_16 = x_154;
x_17 = x_153;
goto block_22;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_155 = lean_ctor_get(x_146, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_146, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_157 = x_146;
} else {
 lean_dec_ref(x_146);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
}
}
}
block_22:
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_5, x_19);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_propagateBeta_spec__6_spec__6(x_1, x_2, x_3, x_4, x_20, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_17);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Array_isEmpty___redArg(x_1);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_st_ref_get(x_3, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_instInhabitedExpr;
x_18 = l_Array_back_x21(lean_box(0), x_17, x_1);
x_19 = l_Lean_Meta_Grind_Goal_getRoot(x_15, x_18, x_9, x_10, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_41 = lean_mk_string_unchecked("grind", 5, 5);
x_42 = lean_mk_string_unchecked("debug", 5, 5);
x_43 = lean_mk_string_unchecked("beta", 4, 4);
x_44 = l_Lean_Name_mkStr3(x_41, x_42, x_43);
lean_inc(x_44);
x_45 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_44, x_9, x_21);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_44);
lean_free_object(x_13);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_22 = x_3;
x_23 = x_4;
x_24 = x_5;
x_25 = x_6;
x_26 = x_7;
x_27 = x_8;
x_28 = x_9;
x_29 = x_10;
x_30 = x_48;
goto block_40;
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_45, 1);
x_51 = lean_ctor_get(x_45, 0);
lean_dec(x_51);
x_52 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_50);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_54 = lean_ctor_get(x_52, 1);
x_55 = lean_ctor_get(x_52, 0);
lean_dec(x_55);
x_56 = lean_mk_string_unchecked("fns: ", 5, 5);
x_57 = l_Lean_stringToMessageData(x_56);
lean_dec(x_56);
lean_inc(x_2);
x_58 = lean_array_to_list(x_2);
x_59 = lean_box(0);
x_60 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_58, x_59);
x_61 = l_Lean_MessageData_ofList(x_60);
lean_ctor_set_tag(x_52, 7);
lean_ctor_set(x_52, 1, x_61);
lean_ctor_set(x_52, 0, x_57);
x_62 = lean_mk_string_unchecked(", lams: ", 8, 8);
x_63 = l_Lean_stringToMessageData(x_62);
lean_dec(x_62);
lean_ctor_set_tag(x_45, 7);
lean_ctor_set(x_45, 1, x_63);
lean_ctor_set(x_45, 0, x_52);
lean_inc(x_1);
x_64 = lean_array_to_list(x_1);
x_65 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_64, x_59);
x_66 = l_Lean_MessageData_ofList(x_65);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_66);
lean_ctor_set(x_13, 0, x_45);
x_67 = lean_mk_string_unchecked("", 0, 0);
x_68 = l_Lean_stringToMessageData(x_67);
lean_dec(x_67);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_13);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_44, x_69, x_7, x_8, x_9, x_10, x_54);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_22 = x_3;
x_23 = x_4;
x_24 = x_5;
x_25 = x_6;
x_26 = x_7;
x_27 = x_8;
x_28 = x_9;
x_29 = x_10;
x_30 = x_71;
goto block_40;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_72 = lean_ctor_get(x_52, 1);
lean_inc(x_72);
lean_dec(x_52);
x_73 = lean_mk_string_unchecked("fns: ", 5, 5);
x_74 = l_Lean_stringToMessageData(x_73);
lean_dec(x_73);
lean_inc(x_2);
x_75 = lean_array_to_list(x_2);
x_76 = lean_box(0);
x_77 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_75, x_76);
x_78 = l_Lean_MessageData_ofList(x_77);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_mk_string_unchecked(", lams: ", 8, 8);
x_81 = l_Lean_stringToMessageData(x_80);
lean_dec(x_80);
lean_ctor_set_tag(x_45, 7);
lean_ctor_set(x_45, 1, x_81);
lean_ctor_set(x_45, 0, x_79);
lean_inc(x_1);
x_82 = lean_array_to_list(x_1);
x_83 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_82, x_76);
x_84 = l_Lean_MessageData_ofList(x_83);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_84);
lean_ctor_set(x_13, 0, x_45);
x_85 = lean_mk_string_unchecked("", 0, 0);
x_86 = l_Lean_stringToMessageData(x_85);
lean_dec(x_85);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_13);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_44, x_87, x_7, x_8, x_9, x_10, x_72);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_22 = x_3;
x_23 = x_4;
x_24 = x_5;
x_25 = x_6;
x_26 = x_7;
x_27 = x_8;
x_28 = x_9;
x_29 = x_10;
x_30 = x_89;
goto block_40;
}
}
else
{
lean_free_object(x_45);
lean_dec(x_44);
lean_dec(x_20);
lean_free_object(x_13);
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
return x_52;
}
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_45, 1);
lean_inc(x_90);
lean_dec(x_45);
x_91 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
x_94 = lean_mk_string_unchecked("fns: ", 5, 5);
x_95 = l_Lean_stringToMessageData(x_94);
lean_dec(x_94);
lean_inc(x_2);
x_96 = lean_array_to_list(x_2);
x_97 = lean_box(0);
x_98 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_96, x_97);
x_99 = l_Lean_MessageData_ofList(x_98);
if (lean_is_scalar(x_93)) {
 x_100 = lean_alloc_ctor(7, 2, 0);
} else {
 x_100 = x_93;
 lean_ctor_set_tag(x_100, 7);
}
lean_ctor_set(x_100, 0, x_95);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_mk_string_unchecked(", lams: ", 8, 8);
x_102 = l_Lean_stringToMessageData(x_101);
lean_dec(x_101);
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_102);
lean_inc(x_1);
x_104 = lean_array_to_list(x_1);
x_105 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_104, x_97);
x_106 = l_Lean_MessageData_ofList(x_105);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_106);
lean_ctor_set(x_13, 0, x_103);
x_107 = lean_mk_string_unchecked("", 0, 0);
x_108 = l_Lean_stringToMessageData(x_107);
lean_dec(x_107);
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_13);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_44, x_109, x_7, x_8, x_9, x_10, x_92);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_22 = x_3;
x_23 = x_4;
x_24 = x_5;
x_25 = x_6;
x_26 = x_7;
x_27 = x_8;
x_28 = x_9;
x_29 = x_10;
x_30 = x_111;
goto block_40;
}
else
{
lean_dec(x_44);
lean_dec(x_20);
lean_free_object(x_13);
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
return x_91;
}
}
}
block_40:
{
lean_object* x_31; size_t x_32; lean_object* x_33; size_t x_34; lean_object* x_35; 
x_31 = lean_box(0);
x_32 = lean_array_size(x_2);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_usize_of_nat(x_33);
x_35 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_propagateBeta_spec__6(x_20, x_1, x_2, x_32, x_34, x_31, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
lean_dec(x_2);
lean_dec(x_1);
lean_dec(x_20);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_31);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
return x_35;
}
}
}
else
{
uint8_t x_112; 
lean_free_object(x_13);
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
x_112 = !lean_is_exclusive(x_19);
if (x_112 == 0)
{
return x_19;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_19, 0);
x_114 = lean_ctor_get(x_19, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_19);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_ctor_get(x_13, 0);
x_117 = lean_ctor_get(x_13, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_13);
x_118 = l_Lean_instInhabitedExpr;
x_119 = l_Array_back_x21(lean_box(0), x_118, x_1);
x_120 = l_Lean_Meta_Grind_Goal_getRoot(x_116, x_119, x_9, x_10, x_117);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_141 = lean_mk_string_unchecked("grind", 5, 5);
x_142 = lean_mk_string_unchecked("debug", 5, 5);
x_143 = lean_mk_string_unchecked("beta", 4, 4);
x_144 = l_Lean_Name_mkStr3(x_141, x_142, x_143);
lean_inc(x_144);
x_145 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_144, x_9, x_122);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_unbox(x_146);
lean_dec(x_146);
if (x_147 == 0)
{
lean_object* x_148; 
lean_dec(x_144);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_dec(x_145);
x_123 = x_3;
x_124 = x_4;
x_125 = x_5;
x_126 = x_6;
x_127 = x_7;
x_128 = x_8;
x_129 = x_9;
x_130 = x_10;
x_131 = x_148;
goto block_140;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_145, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_150 = x_145;
} else {
 lean_dec_ref(x_145);
 x_150 = lean_box(0);
}
x_151 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_149);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
x_154 = lean_mk_string_unchecked("fns: ", 5, 5);
x_155 = l_Lean_stringToMessageData(x_154);
lean_dec(x_154);
lean_inc(x_2);
x_156 = lean_array_to_list(x_2);
x_157 = lean_box(0);
x_158 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_156, x_157);
x_159 = l_Lean_MessageData_ofList(x_158);
if (lean_is_scalar(x_153)) {
 x_160 = lean_alloc_ctor(7, 2, 0);
} else {
 x_160 = x_153;
 lean_ctor_set_tag(x_160, 7);
}
lean_ctor_set(x_160, 0, x_155);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_mk_string_unchecked(", lams: ", 8, 8);
x_162 = l_Lean_stringToMessageData(x_161);
lean_dec(x_161);
if (lean_is_scalar(x_150)) {
 x_163 = lean_alloc_ctor(7, 2, 0);
} else {
 x_163 = x_150;
 lean_ctor_set_tag(x_163, 7);
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_162);
lean_inc(x_1);
x_164 = lean_array_to_list(x_1);
x_165 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_164, x_157);
x_166 = l_Lean_MessageData_ofList(x_165);
x_167 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_167, 0, x_163);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_mk_string_unchecked("", 0, 0);
x_169 = l_Lean_stringToMessageData(x_168);
lean_dec(x_168);
x_170 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_169);
x_171 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_144, x_170, x_7, x_8, x_9, x_10, x_152);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec(x_171);
x_123 = x_3;
x_124 = x_4;
x_125 = x_5;
x_126 = x_6;
x_127 = x_7;
x_128 = x_8;
x_129 = x_9;
x_130 = x_10;
x_131 = x_172;
goto block_140;
}
else
{
lean_dec(x_150);
lean_dec(x_144);
lean_dec(x_121);
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
return x_151;
}
}
block_140:
{
lean_object* x_132; size_t x_133; lean_object* x_134; size_t x_135; lean_object* x_136; 
x_132 = lean_box(0);
x_133 = lean_array_size(x_2);
x_134 = lean_unsigned_to_nat(0u);
x_135 = lean_usize_of_nat(x_134);
x_136 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_propagateBeta_spec__6(x_121, x_1, x_2, x_133, x_135, x_132, x_123, x_124, x_125, x_126, x_127, x_128, x_129, x_130, x_131);
lean_dec(x_2);
lean_dec(x_1);
lean_dec(x_121);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_132);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
else
{
return x_136;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
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
x_173 = lean_ctor_get(x_120, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_120, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_175 = x_120;
} else {
 lean_dec_ref(x_120);
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
}
else
{
lean_object* x_177; lean_object* x_178; 
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
x_177 = lean_box(0);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_11);
return x_178;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_propagateBeta_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_propagateBeta_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_propagateBeta_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_Grind_propagateBeta_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_Grind_propagateBeta_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_Grind_propagateBeta_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_DTreeMap_Internal_Impl_forInStep___at___Lean_Meta_Grind_propagateBeta_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_propagateBeta_spec__6_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_propagateBeta_spec__6_spec__6(x_1, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_propagateBeta_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_propagateBeta_spec__6(x_1, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_st_ref_get(x_4, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_dec(x_3);
lean_inc(x_17);
x_18 = l_Lean_Meta_Grind_Goal_getENode(x_15, x_17, x_10, x_11, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 4);
lean_inc(x_24);
x_25 = lean_ctor_get(x_19, 5);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_19, sizeof(void*)*13);
x_27 = lean_ctor_get(x_19, 6);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_19, sizeof(void*)*13 + 1);
x_29 = lean_ctor_get_uint8(x_19, sizeof(void*)*13 + 2);
x_30 = lean_ctor_get_uint8(x_19, sizeof(void*)*13 + 3);
x_31 = lean_ctor_get_uint8(x_19, sizeof(void*)*13 + 4);
x_32 = lean_ctor_get(x_19, 7);
lean_inc(x_32);
x_33 = lean_ctor_get(x_19, 8);
lean_inc(x_33);
x_34 = lean_ctor_get(x_19, 9);
lean_inc(x_34);
x_35 = lean_ctor_get(x_19, 10);
lean_inc(x_35);
x_36 = lean_ctor_get(x_19, 11);
lean_inc(x_36);
x_37 = lean_ctor_get(x_19, 12);
lean_inc(x_37);
lean_dec(x_19);
lean_inc(x_1);
lean_inc(x_22);
lean_inc(x_21);
x_38 = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_22);
lean_ctor_set(x_38, 2, x_1);
lean_ctor_set(x_38, 3, x_23);
lean_ctor_set(x_38, 4, x_24);
lean_ctor_set(x_38, 5, x_25);
lean_ctor_set(x_38, 6, x_27);
lean_ctor_set(x_38, 7, x_32);
lean_ctor_set(x_38, 8, x_33);
lean_ctor_set(x_38, 9, x_34);
lean_ctor_set(x_38, 10, x_35);
lean_ctor_set(x_38, 11, x_36);
lean_ctor_set(x_38, 12, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*13, x_26);
lean_ctor_set_uint8(x_38, sizeof(void*)*13 + 1, x_28);
lean_ctor_set_uint8(x_38, sizeof(void*)*13 + 2, x_29);
lean_ctor_set_uint8(x_38, sizeof(void*)*13 + 3, x_30);
lean_ctor_set_uint8(x_38, sizeof(void*)*13 + 4, x_31);
x_39 = l_Lean_Meta_Grind_setENode(x_21, x_38, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_39, 1);
x_42 = lean_ctor_get(x_39, 0);
lean_dec(x_42);
x_43 = lean_ptr_addr(x_22);
x_44 = lean_ptr_addr(x_2);
x_45 = lean_usize_dec_eq(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_free_object(x_39);
lean_dec(x_17);
x_46 = lean_box(0);
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_46);
x_3 = x_13;
x_12 = x_41;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_22);
lean_dec(x_1);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_13, 1, x_17);
lean_ctor_set(x_13, 0, x_49);
lean_ctor_set(x_39, 0, x_13);
return x_39;
}
}
else
{
lean_object* x_50; size_t x_51; size_t x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_39, 1);
lean_inc(x_50);
lean_dec(x_39);
x_51 = lean_ptr_addr(x_22);
x_52 = lean_ptr_addr(x_2);
x_53 = lean_usize_dec_eq(x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_17);
x_54 = lean_box(0);
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_54);
x_3 = x_13;
x_12 = x_50;
goto _start;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_22);
lean_dec(x_1);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_13, 1, x_17);
lean_ctor_set(x_13, 0, x_57);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_13);
lean_ctor_set(x_58, 1, x_50);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_17);
lean_free_object(x_13);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_18);
if (x_59 == 0)
{
return x_18;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_18, 0);
x_61 = lean_ctor_get(x_18, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_18);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_13, 0);
x_64 = lean_ctor_get(x_13, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_13);
x_65 = lean_ctor_get(x_3, 1);
lean_inc(x_65);
lean_dec(x_3);
lean_inc(x_65);
x_66 = l_Lean_Meta_Grind_Goal_getENode(x_63, x_65, x_10, x_11, x_64);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; size_t x_90; size_t x_91; uint8_t x_92; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_67, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_67, 5);
lean_inc(x_73);
x_74 = lean_ctor_get_uint8(x_67, sizeof(void*)*13);
x_75 = lean_ctor_get(x_67, 6);
lean_inc(x_75);
x_76 = lean_ctor_get_uint8(x_67, sizeof(void*)*13 + 1);
x_77 = lean_ctor_get_uint8(x_67, sizeof(void*)*13 + 2);
x_78 = lean_ctor_get_uint8(x_67, sizeof(void*)*13 + 3);
x_79 = lean_ctor_get_uint8(x_67, sizeof(void*)*13 + 4);
x_80 = lean_ctor_get(x_67, 7);
lean_inc(x_80);
x_81 = lean_ctor_get(x_67, 8);
lean_inc(x_81);
x_82 = lean_ctor_get(x_67, 9);
lean_inc(x_82);
x_83 = lean_ctor_get(x_67, 10);
lean_inc(x_83);
x_84 = lean_ctor_get(x_67, 11);
lean_inc(x_84);
x_85 = lean_ctor_get(x_67, 12);
lean_inc(x_85);
lean_dec(x_67);
lean_inc(x_1);
lean_inc(x_70);
lean_inc(x_69);
x_86 = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(x_86, 0, x_69);
lean_ctor_set(x_86, 1, x_70);
lean_ctor_set(x_86, 2, x_1);
lean_ctor_set(x_86, 3, x_71);
lean_ctor_set(x_86, 4, x_72);
lean_ctor_set(x_86, 5, x_73);
lean_ctor_set(x_86, 6, x_75);
lean_ctor_set(x_86, 7, x_80);
lean_ctor_set(x_86, 8, x_81);
lean_ctor_set(x_86, 9, x_82);
lean_ctor_set(x_86, 10, x_83);
lean_ctor_set(x_86, 11, x_84);
lean_ctor_set(x_86, 12, x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*13, x_74);
lean_ctor_set_uint8(x_86, sizeof(void*)*13 + 1, x_76);
lean_ctor_set_uint8(x_86, sizeof(void*)*13 + 2, x_77);
lean_ctor_set_uint8(x_86, sizeof(void*)*13 + 3, x_78);
lean_ctor_set_uint8(x_86, sizeof(void*)*13 + 4, x_79);
x_87 = l_Lean_Meta_Grind_setENode(x_69, x_86, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_68);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = lean_ptr_addr(x_70);
x_91 = lean_ptr_addr(x_2);
x_92 = lean_usize_dec_eq(x_90, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_89);
lean_dec(x_65);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_70);
x_3 = x_94;
x_12 = x_88;
goto _start;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_70);
lean_dec(x_1);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_65);
if (lean_is_scalar(x_89)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_89;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_88);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_65);
lean_dec(x_1);
x_100 = lean_ctor_get(x_66, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_66, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_102 = x_66;
} else {
 lean_dec_ref(x_66);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(0);
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
x_14 = l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(x_2, x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 4);
lean_inc(x_14);
lean_dec(x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
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
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Lean_Meta_Grind_propagateUp(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_1 = x_20;
x_2 = x_14;
x_11 = x_19;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_12);
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
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_11);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l_Lean_Meta_Grind_propagateDown(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_1 = x_14;
x_2 = x_17;
x_11 = x_16;
goto _start;
}
else
{
lean_dec(x_14);
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
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_578; lean_object* x_579; uint8_t x_580; 
x_235 = lean_mk_string_unchecked("grind", 5, 5);
x_236 = lean_mk_string_unchecked("debug", 5, 5);
x_237 = l_Lean_Name_mkStr2(x_235, x_236);
lean_inc(x_237);
x_578 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_237, x_16, x_18);
x_579 = lean_ctor_get(x_578, 0);
lean_inc(x_579);
x_580 = lean_unbox(x_579);
lean_dec(x_579);
if (x_580 == 0)
{
lean_object* x_581; 
x_581 = lean_ctor_get(x_578, 1);
lean_inc(x_581);
lean_dec(x_578);
x_521 = x_10;
x_522 = x_11;
x_523 = x_12;
x_524 = x_13;
x_525 = x_14;
x_526 = x_15;
x_527 = x_16;
x_528 = x_17;
x_529 = x_581;
goto block_577;
}
else
{
uint8_t x_582; 
x_582 = !lean_is_exclusive(x_578);
if (x_582 == 0)
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_583 = lean_ctor_get(x_578, 1);
x_584 = lean_ctor_get(x_578, 0);
lean_dec(x_584);
x_585 = l_Lean_Meta_Grind_updateLastTag(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_583);
if (lean_obj_tag(x_585) == 0)
{
uint8_t x_586; 
x_586 = !lean_is_exclusive(x_585);
if (x_586 == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_587 = lean_ctor_get(x_585, 1);
x_588 = lean_ctor_get(x_585, 0);
lean_dec(x_588);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_3);
x_589 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_3, x_10, x_14, x_15, x_16, x_17, x_587);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_589, 1);
lean_inc(x_591);
lean_dec(x_589);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_4);
x_592 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_4, x_10, x_14, x_15, x_16, x_17, x_591);
if (lean_obj_tag(x_592) == 0)
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_592, 1);
lean_inc(x_594);
lean_dec(x_592);
x_595 = lean_mk_string_unchecked("adding ", 7, 7);
x_596 = l_Lean_stringToMessageData(x_595);
lean_dec(x_595);
lean_ctor_set_tag(x_585, 7);
lean_ctor_set(x_585, 1, x_590);
lean_ctor_set(x_585, 0, x_596);
x_597 = lean_mk_string_unchecked(" ↦ ", 5, 3);
x_598 = l_Lean_stringToMessageData(x_597);
lean_dec(x_597);
lean_ctor_set_tag(x_578, 7);
lean_ctor_set(x_578, 1, x_598);
lean_ctor_set(x_578, 0, x_585);
x_599 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_599, 0, x_578);
lean_ctor_set(x_599, 1, x_593);
x_600 = lean_mk_string_unchecked("", 0, 0);
x_601 = l_Lean_stringToMessageData(x_600);
lean_dec(x_600);
x_602 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_602, 0, x_599);
lean_ctor_set(x_602, 1, x_601);
lean_inc(x_237);
x_603 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_237, x_602, x_14, x_15, x_16, x_17, x_594);
x_604 = lean_ctor_get(x_603, 1);
lean_inc(x_604);
lean_dec(x_603);
x_521 = x_10;
x_522 = x_11;
x_523 = x_12;
x_524 = x_13;
x_525 = x_14;
x_526 = x_15;
x_527 = x_16;
x_528 = x_17;
x_529 = x_604;
goto block_577;
}
else
{
uint8_t x_605; 
lean_dec(x_590);
lean_free_object(x_585);
lean_free_object(x_578);
lean_dec(x_237);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_605 = !lean_is_exclusive(x_592);
if (x_605 == 0)
{
return x_592;
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_606 = lean_ctor_get(x_592, 0);
x_607 = lean_ctor_get(x_592, 1);
lean_inc(x_607);
lean_inc(x_606);
lean_dec(x_592);
x_608 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_608, 0, x_606);
lean_ctor_set(x_608, 1, x_607);
return x_608;
}
}
}
else
{
uint8_t x_609; 
lean_free_object(x_585);
lean_free_object(x_578);
lean_dec(x_237);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_609 = !lean_is_exclusive(x_589);
if (x_609 == 0)
{
return x_589;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_610 = lean_ctor_get(x_589, 0);
x_611 = lean_ctor_get(x_589, 1);
lean_inc(x_611);
lean_inc(x_610);
lean_dec(x_589);
x_612 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_612, 0, x_610);
lean_ctor_set(x_612, 1, x_611);
return x_612;
}
}
}
else
{
lean_object* x_613; lean_object* x_614; 
x_613 = lean_ctor_get(x_585, 1);
lean_inc(x_613);
lean_dec(x_585);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_3);
x_614 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_3, x_10, x_14, x_15, x_16, x_17, x_613);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_615 = lean_ctor_get(x_614, 0);
lean_inc(x_615);
x_616 = lean_ctor_get(x_614, 1);
lean_inc(x_616);
lean_dec(x_614);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_4);
x_617 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_4, x_10, x_14, x_15, x_16, x_17, x_616);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_617, 1);
lean_inc(x_619);
lean_dec(x_617);
x_620 = lean_mk_string_unchecked("adding ", 7, 7);
x_621 = l_Lean_stringToMessageData(x_620);
lean_dec(x_620);
x_622 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_615);
x_623 = lean_mk_string_unchecked(" ↦ ", 5, 3);
x_624 = l_Lean_stringToMessageData(x_623);
lean_dec(x_623);
lean_ctor_set_tag(x_578, 7);
lean_ctor_set(x_578, 1, x_624);
lean_ctor_set(x_578, 0, x_622);
x_625 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_625, 0, x_578);
lean_ctor_set(x_625, 1, x_618);
x_626 = lean_mk_string_unchecked("", 0, 0);
x_627 = l_Lean_stringToMessageData(x_626);
lean_dec(x_626);
x_628 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_628, 0, x_625);
lean_ctor_set(x_628, 1, x_627);
lean_inc(x_237);
x_629 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_237, x_628, x_14, x_15, x_16, x_17, x_619);
x_630 = lean_ctor_get(x_629, 1);
lean_inc(x_630);
lean_dec(x_629);
x_521 = x_10;
x_522 = x_11;
x_523 = x_12;
x_524 = x_13;
x_525 = x_14;
x_526 = x_15;
x_527 = x_16;
x_528 = x_17;
x_529 = x_630;
goto block_577;
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
lean_dec(x_615);
lean_free_object(x_578);
lean_dec(x_237);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_631 = lean_ctor_get(x_617, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_617, 1);
lean_inc(x_632);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 lean_ctor_release(x_617, 1);
 x_633 = x_617;
} else {
 lean_dec_ref(x_617);
 x_633 = lean_box(0);
}
if (lean_is_scalar(x_633)) {
 x_634 = lean_alloc_ctor(1, 2, 0);
} else {
 x_634 = x_633;
}
lean_ctor_set(x_634, 0, x_631);
lean_ctor_set(x_634, 1, x_632);
return x_634;
}
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
lean_free_object(x_578);
lean_dec(x_237);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_635 = lean_ctor_get(x_614, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_614, 1);
lean_inc(x_636);
if (lean_is_exclusive(x_614)) {
 lean_ctor_release(x_614, 0);
 lean_ctor_release(x_614, 1);
 x_637 = x_614;
} else {
 lean_dec_ref(x_614);
 x_637 = lean_box(0);
}
if (lean_is_scalar(x_637)) {
 x_638 = lean_alloc_ctor(1, 2, 0);
} else {
 x_638 = x_637;
}
lean_ctor_set(x_638, 0, x_635);
lean_ctor_set(x_638, 1, x_636);
return x_638;
}
}
}
else
{
lean_free_object(x_578);
lean_dec(x_237);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_585;
}
}
else
{
lean_object* x_639; lean_object* x_640; 
x_639 = lean_ctor_get(x_578, 1);
lean_inc(x_639);
lean_dec(x_578);
x_640 = l_Lean_Meta_Grind_updateLastTag(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_639);
if (lean_obj_tag(x_640) == 0)
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_641 = lean_ctor_get(x_640, 1);
lean_inc(x_641);
if (lean_is_exclusive(x_640)) {
 lean_ctor_release(x_640, 0);
 lean_ctor_release(x_640, 1);
 x_642 = x_640;
} else {
 lean_dec_ref(x_640);
 x_642 = lean_box(0);
}
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_3);
x_643 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_3, x_10, x_14, x_15, x_16, x_17, x_641);
if (lean_obj_tag(x_643) == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_644 = lean_ctor_get(x_643, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_643, 1);
lean_inc(x_645);
lean_dec(x_643);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_4);
x_646 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_4, x_10, x_14, x_15, x_16, x_17, x_645);
if (lean_obj_tag(x_646) == 0)
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_647 = lean_ctor_get(x_646, 0);
lean_inc(x_647);
x_648 = lean_ctor_get(x_646, 1);
lean_inc(x_648);
lean_dec(x_646);
x_649 = lean_mk_string_unchecked("adding ", 7, 7);
x_650 = l_Lean_stringToMessageData(x_649);
lean_dec(x_649);
if (lean_is_scalar(x_642)) {
 x_651 = lean_alloc_ctor(7, 2, 0);
} else {
 x_651 = x_642;
 lean_ctor_set_tag(x_651, 7);
}
lean_ctor_set(x_651, 0, x_650);
lean_ctor_set(x_651, 1, x_644);
x_652 = lean_mk_string_unchecked(" ↦ ", 5, 3);
x_653 = l_Lean_stringToMessageData(x_652);
lean_dec(x_652);
x_654 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_654, 0, x_651);
lean_ctor_set(x_654, 1, x_653);
x_655 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_655, 0, x_654);
lean_ctor_set(x_655, 1, x_647);
x_656 = lean_mk_string_unchecked("", 0, 0);
x_657 = l_Lean_stringToMessageData(x_656);
lean_dec(x_656);
x_658 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_658, 0, x_655);
lean_ctor_set(x_658, 1, x_657);
lean_inc(x_237);
x_659 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_237, x_658, x_14, x_15, x_16, x_17, x_648);
x_660 = lean_ctor_get(x_659, 1);
lean_inc(x_660);
lean_dec(x_659);
x_521 = x_10;
x_522 = x_11;
x_523 = x_12;
x_524 = x_13;
x_525 = x_14;
x_526 = x_15;
x_527 = x_16;
x_528 = x_17;
x_529 = x_660;
goto block_577;
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_644);
lean_dec(x_642);
lean_dec(x_237);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_661 = lean_ctor_get(x_646, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_646, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_646)) {
 lean_ctor_release(x_646, 0);
 lean_ctor_release(x_646, 1);
 x_663 = x_646;
} else {
 lean_dec_ref(x_646);
 x_663 = lean_box(0);
}
if (lean_is_scalar(x_663)) {
 x_664 = lean_alloc_ctor(1, 2, 0);
} else {
 x_664 = x_663;
}
lean_ctor_set(x_664, 0, x_661);
lean_ctor_set(x_664, 1, x_662);
return x_664;
}
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
lean_dec(x_642);
lean_dec(x_237);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_665 = lean_ctor_get(x_643, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_643, 1);
lean_inc(x_666);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_667 = x_643;
} else {
 lean_dec_ref(x_643);
 x_667 = lean_box(0);
}
if (lean_is_scalar(x_667)) {
 x_668 = lean_alloc_ctor(1, 2, 0);
} else {
 x_668 = x_667;
}
lean_ctor_set(x_668, 0, x_665);
lean_ctor_set(x_668, 1, x_666);
return x_668;
}
}
else
{
lean_dec(x_237);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_640;
}
}
}
block_57:
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l_Lean_Meta_Grind_isInconsistent___redArg(x_24, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_box(0);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_38 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(x_37, x_22, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_40 = l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(x_23, x_37, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_42 = l_Lean_Meta_Grind_propagateOffset(x_19, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_44 = l_Lean_Meta_Grind_propagateCutsat(x_21, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_Meta_Grind_propagateCommRing(x_20, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_45);
return x_46;
}
else
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_20);
return x_44;
}
}
else
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
return x_42;
}
}
else
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
return x_40;
}
}
else
{
uint8_t x_47; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_47 = !lean_is_exclusive(x_38);
if (x_47 == 0)
{
return x_38;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_38, 0);
x_49 = lean_ctor_get(x_38, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_38);
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
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_51 = !lean_is_exclusive(x_33);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_33, 0);
lean_dec(x_52);
x_53 = lean_box(0);
lean_ctor_set(x_33, 0, x_53);
return x_33;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_33, 1);
lean_inc(x_54);
lean_dec(x_33);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
block_132:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_87 = lean_ctor_get(x_8, 7);
lean_inc(x_87);
x_88 = lean_ctor_get(x_8, 8);
lean_inc(x_88);
x_89 = lean_ctor_get(x_8, 9);
lean_inc(x_89);
x_90 = lean_ctor_get(x_8, 10);
lean_inc(x_90);
x_91 = lean_ctor_get(x_8, 11);
lean_inc(x_91);
x_92 = lean_ctor_get(x_8, 12);
lean_inc(x_92);
lean_inc(x_81);
x_93 = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(x_93, 0, x_81);
lean_ctor_set(x_93, 1, x_74);
lean_ctor_set(x_93, 2, x_80);
lean_ctor_set(x_93, 3, x_79);
lean_ctor_set(x_93, 4, x_63);
lean_ctor_set(x_93, 5, x_75);
lean_ctor_set(x_93, 6, x_62);
lean_ctor_set(x_93, 7, x_87);
lean_ctor_set(x_93, 8, x_88);
lean_ctor_set(x_93, 9, x_89);
lean_ctor_set(x_93, 10, x_90);
lean_ctor_set(x_93, 11, x_91);
lean_ctor_set(x_93, 12, x_92);
lean_ctor_set_uint8(x_93, sizeof(void*)*13, x_77);
lean_ctor_set_uint8(x_93, sizeof(void*)*13 + 1, x_73);
lean_ctor_set_uint8(x_93, sizeof(void*)*13 + 2, x_58);
lean_ctor_set_uint8(x_93, sizeof(void*)*13 + 3, x_83);
lean_ctor_set_uint8(x_93, sizeof(void*)*13 + 4, x_86);
lean_inc(x_71);
x_94 = l_Lean_Meta_Grind_setENode(x_71, x_93, x_70, x_61, x_82, x_72, x_78, x_64, x_66, x_76, x_67);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
lean_inc(x_76);
lean_inc(x_66);
lean_inc(x_64);
lean_inc(x_78);
lean_inc(x_72);
lean_inc(x_82);
lean_inc(x_61);
lean_inc(x_70);
x_96 = l_Lean_Meta_Grind_propagateBeta(x_60, x_84, x_70, x_61, x_82, x_72, x_78, x_64, x_66, x_76, x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
lean_inc(x_76);
lean_inc(x_66);
lean_inc(x_64);
lean_inc(x_78);
lean_inc(x_72);
lean_inc(x_82);
lean_inc(x_61);
lean_inc(x_70);
x_98 = l_Lean_Meta_Grind_propagateBeta(x_65, x_68, x_70, x_61, x_82, x_72, x_78, x_64, x_66, x_76, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
lean_inc(x_7);
lean_inc(x_8);
x_100 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_checkOffsetEq(x_8, x_7, x_70, x_61, x_82, x_72, x_78, x_64, x_66, x_76, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_7);
lean_inc(x_8);
x_103 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_checkCutsatEq(x_8, x_7, x_70, x_61, x_82, x_72, x_78, x_64, x_66, x_76, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_checkCommRingEq(x_8, x_7, x_70, x_61, x_82, x_72, x_78, x_64, x_66, x_76, x_105);
lean_dec(x_7);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l_Lean_Meta_Grind_resetParentsOf(x_69, x_70, x_61, x_82, x_72, x_78, x_64, x_66, x_76, x_108);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
lean_inc(x_59);
x_111 = l_Lean_Meta_Grind_copyParentsTo(x_59, x_71, x_70, x_61, x_82, x_72, x_78, x_64, x_66, x_76, x_110);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = l_Lean_Meta_Grind_isInconsistent___redArg(x_70, x_112);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_unbox(x_114);
lean_dec(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_117 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(x_81, x_70, x_61, x_82, x_72, x_78, x_64, x_66, x_76, x_116);
lean_dec(x_81);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_19 = x_101;
x_20 = x_107;
x_21 = x_104;
x_22 = x_59;
x_23 = x_85;
x_24 = x_70;
x_25 = x_61;
x_26 = x_82;
x_27 = x_72;
x_28 = x_78;
x_29 = x_64;
x_30 = x_66;
x_31 = x_76;
x_32 = x_118;
goto block_57;
}
else
{
lean_dec(x_107);
lean_dec(x_104);
lean_dec(x_101);
lean_dec(x_85);
lean_dec(x_82);
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_72);
lean_dec(x_70);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_59);
return x_117;
}
}
else
{
lean_object* x_119; 
lean_dec(x_81);
x_119 = lean_ctor_get(x_113, 1);
lean_inc(x_119);
lean_dec(x_113);
x_19 = x_101;
x_20 = x_107;
x_21 = x_104;
x_22 = x_59;
x_23 = x_85;
x_24 = x_70;
x_25 = x_61;
x_26 = x_82;
x_27 = x_72;
x_28 = x_78;
x_29 = x_64;
x_30 = x_66;
x_31 = x_76;
x_32 = x_119;
goto block_57;
}
}
else
{
uint8_t x_120; 
lean_dec(x_104);
lean_dec(x_101);
lean_dec(x_85);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_59);
x_120 = !lean_is_exclusive(x_106);
if (x_120 == 0)
{
return x_106;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_106, 0);
x_122 = lean_ctor_get(x_106, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_106);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_101);
lean_dec(x_85);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_8);
lean_dec(x_7);
x_124 = !lean_is_exclusive(x_103);
if (x_124 == 0)
{
return x_103;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_103, 0);
x_126 = lean_ctor_get(x_103, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_103);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_85);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_8);
lean_dec(x_7);
x_128 = !lean_is_exclusive(x_100);
if (x_128 == 0)
{
return x_100;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_100, 0);
x_130 = lean_ctor_get(x_100, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_100);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
lean_dec(x_85);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_8);
lean_dec(x_7);
return x_98;
}
}
else
{
lean_dec(x_85);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_8);
lean_dec(x_7);
return x_96;
}
}
block_163:
{
if (x_2 == 0)
{
uint8_t x_161; 
x_161 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 4);
if (x_161 == 0)
{
uint8_t x_162; 
x_162 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 4);
x_58 = x_133;
x_59 = x_134;
x_60 = x_135;
x_61 = x_136;
x_62 = x_137;
x_63 = x_138;
x_64 = x_139;
x_65 = x_140;
x_66 = x_143;
x_67 = x_142;
x_68 = x_141;
x_69 = x_144;
x_70 = x_145;
x_71 = x_146;
x_72 = x_147;
x_73 = x_148;
x_74 = x_149;
x_75 = x_150;
x_76 = x_151;
x_77 = x_152;
x_78 = x_153;
x_79 = x_154;
x_80 = x_155;
x_81 = x_156;
x_82 = x_157;
x_83 = x_160;
x_84 = x_158;
x_85 = x_159;
x_86 = x_162;
goto block_132;
}
else
{
x_58 = x_133;
x_59 = x_134;
x_60 = x_135;
x_61 = x_136;
x_62 = x_137;
x_63 = x_138;
x_64 = x_139;
x_65 = x_140;
x_66 = x_143;
x_67 = x_142;
x_68 = x_141;
x_69 = x_144;
x_70 = x_145;
x_71 = x_146;
x_72 = x_147;
x_73 = x_148;
x_74 = x_149;
x_75 = x_150;
x_76 = x_151;
x_77 = x_152;
x_78 = x_153;
x_79 = x_154;
x_80 = x_155;
x_81 = x_156;
x_82 = x_157;
x_83 = x_160;
x_84 = x_158;
x_85 = x_159;
x_86 = x_161;
goto block_132;
}
}
else
{
x_58 = x_133;
x_59 = x_134;
x_60 = x_135;
x_61 = x_136;
x_62 = x_137;
x_63 = x_138;
x_64 = x_139;
x_65 = x_140;
x_66 = x_143;
x_67 = x_142;
x_68 = x_141;
x_69 = x_144;
x_70 = x_145;
x_71 = x_146;
x_72 = x_147;
x_73 = x_148;
x_74 = x_149;
x_75 = x_150;
x_76 = x_151;
x_77 = x_152;
x_78 = x_153;
x_79 = x_154;
x_80 = x_155;
x_81 = x_156;
x_82 = x_157;
x_83 = x_160;
x_84 = x_158;
x_85 = x_159;
x_86 = x_2;
goto block_132;
}
}
block_234:
{
lean_object* x_181; 
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_169);
x_181 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(x_169, x_172, x_173, x_174, x_175, x_176, x_177, x_178, x_179, x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_st_ref_get(x_172, x_182);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = lean_st_ref_get(x_172, x_185);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
lean_inc(x_164);
x_189 = l_Lean_Meta_Grind_Goal_getENode(x_187, x_164, x_178, x_179, x_188);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_ctor_get(x_190, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_8, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_190, 2);
lean_inc(x_194);
x_195 = lean_ctor_get(x_190, 3);
lean_inc(x_195);
x_196 = lean_ctor_get(x_190, 4);
lean_inc(x_196);
x_197 = lean_ctor_get(x_190, 5);
lean_inc(x_197);
x_198 = lean_ctor_get_uint8(x_190, sizeof(void*)*13);
x_199 = lean_ctor_get(x_190, 6);
lean_inc(x_199);
x_200 = lean_ctor_get_uint8(x_190, sizeof(void*)*13 + 1);
x_201 = lean_ctor_get_uint8(x_190, sizeof(void*)*13 + 2);
x_202 = lean_ctor_get_uint8(x_190, sizeof(void*)*13 + 3);
x_203 = lean_ctor_get_uint8(x_190, sizeof(void*)*13 + 4);
x_204 = lean_ctor_get(x_190, 7);
lean_inc(x_204);
x_205 = lean_ctor_get(x_190, 8);
lean_inc(x_205);
x_206 = lean_ctor_get(x_190, 9);
lean_inc(x_206);
x_207 = lean_ctor_get(x_190, 10);
lean_inc(x_207);
x_208 = lean_ctor_get(x_190, 11);
lean_inc(x_208);
x_209 = lean_ctor_get(x_190, 12);
lean_inc(x_209);
lean_dec(x_190);
x_210 = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(x_210, 0, x_192);
lean_ctor_set(x_210, 1, x_193);
lean_ctor_set(x_210, 2, x_194);
lean_ctor_set(x_210, 3, x_195);
lean_ctor_set(x_210, 4, x_196);
lean_ctor_set(x_210, 5, x_197);
lean_ctor_set(x_210, 6, x_199);
lean_ctor_set(x_210, 7, x_204);
lean_ctor_set(x_210, 8, x_205);
lean_ctor_set(x_210, 9, x_206);
lean_ctor_set(x_210, 10, x_207);
lean_ctor_set(x_210, 11, x_208);
lean_ctor_set(x_210, 12, x_209);
lean_ctor_set_uint8(x_210, sizeof(void*)*13, x_198);
lean_ctor_set_uint8(x_210, sizeof(void*)*13 + 1, x_200);
lean_ctor_set_uint8(x_210, sizeof(void*)*13 + 2, x_201);
lean_ctor_set_uint8(x_210, sizeof(void*)*13 + 3, x_202);
lean_ctor_set_uint8(x_210, sizeof(void*)*13 + 4, x_203);
x_211 = l_Lean_Meta_Grind_setENode(x_165, x_210, x_172, x_173, x_174, x_175, x_176, x_177, x_178, x_179, x_191);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_213 = l_Lean_Meta_Grind_Goal_getEqc(x_184, x_3);
x_214 = lean_ctor_get(x_8, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_7, 1);
lean_inc(x_215);
x_216 = lean_ctor_get(x_8, 2);
lean_inc(x_216);
x_217 = lean_ctor_get(x_8, 3);
lean_inc(x_217);
x_218 = lean_ctor_get(x_8, 4);
lean_inc(x_218);
x_219 = lean_ctor_get(x_8, 5);
lean_inc(x_219);
x_220 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_221 = lean_ctor_get(x_8, 6);
lean_inc(x_221);
x_222 = lean_ctor_get(x_7, 6);
lean_inc(x_222);
x_223 = lean_nat_add(x_221, x_222);
lean_dec(x_222);
lean_dec(x_221);
x_224 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 3);
if (x_224 == 0)
{
uint8_t x_225; uint8_t x_226; uint8_t x_227; 
x_225 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_226 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 2);
x_227 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 3);
x_133 = x_226;
x_134 = x_169;
x_135 = x_171;
x_136 = x_173;
x_137 = x_223;
x_138 = x_218;
x_139 = x_177;
x_140 = x_168;
x_141 = x_170;
x_142 = x_212;
x_143 = x_178;
x_144 = x_164;
x_145 = x_172;
x_146 = x_166;
x_147 = x_175;
x_148 = x_225;
x_149 = x_215;
x_150 = x_219;
x_151 = x_179;
x_152 = x_220;
x_153 = x_176;
x_154 = x_217;
x_155 = x_216;
x_156 = x_214;
x_157 = x_174;
x_158 = x_167;
x_159 = x_213;
x_160 = x_227;
goto block_163;
}
else
{
uint8_t x_228; uint8_t x_229; 
x_228 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_229 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 2);
x_133 = x_229;
x_134 = x_169;
x_135 = x_171;
x_136 = x_173;
x_137 = x_223;
x_138 = x_218;
x_139 = x_177;
x_140 = x_168;
x_141 = x_170;
x_142 = x_212;
x_143 = x_178;
x_144 = x_164;
x_145 = x_172;
x_146 = x_166;
x_147 = x_175;
x_148 = x_228;
x_149 = x_215;
x_150 = x_219;
x_151 = x_179;
x_152 = x_220;
x_153 = x_176;
x_154 = x_217;
x_155 = x_216;
x_156 = x_214;
x_157 = x_174;
x_158 = x_167;
x_159 = x_213;
x_160 = x_224;
goto block_163;
}
}
else
{
uint8_t x_230; 
lean_dec(x_184);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_230 = !lean_is_exclusive(x_189);
if (x_230 == 0)
{
return x_189;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_189, 0);
x_232 = lean_ctor_get(x_189, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_189);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
else
{
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_181;
}
}
block_495:
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_7, 0);
lean_inc(x_252);
x_253 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(x_252, x_243, x_244, x_245, x_246, x_247, x_248, x_249, x_250, x_251);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = lean_ctor_get(x_6, 2);
lean_inc(x_256);
lean_dec(x_6);
lean_inc(x_256);
lean_inc(x_3);
x_257 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(x_3, x_256, x_243, x_244, x_245, x_246, x_247, x_248, x_249, x_250, x_255);
if (lean_obj_tag(x_257) == 0)
{
uint8_t x_258; 
x_258 = !lean_is_exclusive(x_257);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_259 = lean_ctor_get(x_257, 1);
x_260 = lean_ctor_get(x_257, 0);
lean_dec(x_260);
lean_inc(x_237);
x_261 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_237, x_249, x_259);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_unbox(x_262);
lean_dec(x_262);
if (x_263 == 0)
{
lean_object* x_264; 
lean_free_object(x_257);
lean_dec(x_237);
x_264 = lean_ctor_get(x_261, 1);
lean_inc(x_264);
lean_dec(x_261);
x_164 = x_252;
x_165 = x_238;
x_166 = x_256;
x_167 = x_240;
x_168 = x_239;
x_169 = x_254;
x_170 = x_242;
x_171 = x_241;
x_172 = x_243;
x_173 = x_244;
x_174 = x_245;
x_175 = x_246;
x_176 = x_247;
x_177 = x_248;
x_178 = x_249;
x_179 = x_250;
x_180 = x_264;
goto block_234;
}
else
{
uint8_t x_265; 
x_265 = !lean_is_exclusive(x_261);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_261, 1);
x_267 = lean_ctor_get(x_261, 0);
lean_dec(x_267);
x_268 = l_Lean_Meta_Grind_updateLastTag(x_243, x_244, x_245, x_246, x_247, x_248, x_249, x_250, x_266);
if (lean_obj_tag(x_268) == 0)
{
uint8_t x_269; 
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_268, 1);
x_271 = lean_ctor_get(x_268, 0);
lean_dec(x_271);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_3);
x_272 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_3, x_243, x_247, x_248, x_249, x_250, x_270);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_256);
x_275 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_256, x_243, x_247, x_248, x_249, x_250, x_274);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
x_278 = lean_st_ref_get(x_243, x_277);
x_279 = !lean_is_exclusive(x_278);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_278, 0);
x_281 = lean_ctor_get(x_278, 1);
lean_inc(x_3);
x_282 = l_Lean_Meta_Grind_Goal_getRoot(x_280, x_3, x_249, x_250, x_281);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
x_285 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_283, x_243, x_247, x_248, x_249, x_250, x_284);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = lean_mk_string_unchecked("", 0, 0);
x_289 = l_Lean_stringToMessageData(x_288);
lean_dec(x_288);
lean_inc(x_289);
lean_ctor_set_tag(x_278, 7);
lean_ctor_set(x_278, 1, x_273);
lean_ctor_set(x_278, 0, x_289);
x_290 = lean_mk_string_unchecked(" new root ", 10, 10);
x_291 = l_Lean_stringToMessageData(x_290);
lean_dec(x_290);
lean_ctor_set_tag(x_268, 7);
lean_ctor_set(x_268, 1, x_291);
lean_ctor_set(x_268, 0, x_278);
lean_ctor_set_tag(x_261, 7);
lean_ctor_set(x_261, 1, x_276);
lean_ctor_set(x_261, 0, x_268);
x_292 = lean_mk_string_unchecked(", ", 2, 2);
x_293 = l_Lean_stringToMessageData(x_292);
lean_dec(x_292);
lean_ctor_set_tag(x_257, 7);
lean_ctor_set(x_257, 1, x_293);
lean_ctor_set(x_257, 0, x_261);
x_294 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_294, 0, x_257);
lean_ctor_set(x_294, 1, x_286);
x_295 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_289);
x_296 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_237, x_295, x_247, x_248, x_249, x_250, x_287);
x_297 = lean_ctor_get(x_296, 1);
lean_inc(x_297);
lean_dec(x_296);
x_164 = x_252;
x_165 = x_238;
x_166 = x_256;
x_167 = x_240;
x_168 = x_239;
x_169 = x_254;
x_170 = x_242;
x_171 = x_241;
x_172 = x_243;
x_173 = x_244;
x_174 = x_245;
x_175 = x_246;
x_176 = x_247;
x_177 = x_248;
x_178 = x_249;
x_179 = x_250;
x_180 = x_297;
goto block_234;
}
else
{
uint8_t x_298; 
lean_free_object(x_278);
lean_dec(x_276);
lean_dec(x_273);
lean_free_object(x_268);
lean_free_object(x_261);
lean_free_object(x_257);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_298 = !lean_is_exclusive(x_285);
if (x_298 == 0)
{
return x_285;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_285, 0);
x_300 = lean_ctor_get(x_285, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_285);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
}
}
else
{
uint8_t x_302; 
lean_free_object(x_278);
lean_dec(x_276);
lean_dec(x_273);
lean_free_object(x_268);
lean_free_object(x_261);
lean_free_object(x_257);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_302 = !lean_is_exclusive(x_282);
if (x_302 == 0)
{
return x_282;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_282, 0);
x_304 = lean_ctor_get(x_282, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_282);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
return x_305;
}
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_278, 0);
x_307 = lean_ctor_get(x_278, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_278);
lean_inc(x_3);
x_308 = l_Lean_Meta_Grind_Goal_getRoot(x_306, x_3, x_249, x_250, x_307);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec(x_308);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
x_311 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_309, x_243, x_247, x_248, x_249, x_250, x_310);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec(x_311);
x_314 = lean_mk_string_unchecked("", 0, 0);
x_315 = l_Lean_stringToMessageData(x_314);
lean_dec(x_314);
lean_inc(x_315);
x_316 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_273);
x_317 = lean_mk_string_unchecked(" new root ", 10, 10);
x_318 = l_Lean_stringToMessageData(x_317);
lean_dec(x_317);
lean_ctor_set_tag(x_268, 7);
lean_ctor_set(x_268, 1, x_318);
lean_ctor_set(x_268, 0, x_316);
lean_ctor_set_tag(x_261, 7);
lean_ctor_set(x_261, 1, x_276);
lean_ctor_set(x_261, 0, x_268);
x_319 = lean_mk_string_unchecked(", ", 2, 2);
x_320 = l_Lean_stringToMessageData(x_319);
lean_dec(x_319);
lean_ctor_set_tag(x_257, 7);
lean_ctor_set(x_257, 1, x_320);
lean_ctor_set(x_257, 0, x_261);
x_321 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_321, 0, x_257);
lean_ctor_set(x_321, 1, x_312);
x_322 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_315);
x_323 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_237, x_322, x_247, x_248, x_249, x_250, x_313);
x_324 = lean_ctor_get(x_323, 1);
lean_inc(x_324);
lean_dec(x_323);
x_164 = x_252;
x_165 = x_238;
x_166 = x_256;
x_167 = x_240;
x_168 = x_239;
x_169 = x_254;
x_170 = x_242;
x_171 = x_241;
x_172 = x_243;
x_173 = x_244;
x_174 = x_245;
x_175 = x_246;
x_176 = x_247;
x_177 = x_248;
x_178 = x_249;
x_179 = x_250;
x_180 = x_324;
goto block_234;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_276);
lean_dec(x_273);
lean_free_object(x_268);
lean_free_object(x_261);
lean_free_object(x_257);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_325 = lean_ctor_get(x_311, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_311, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_327 = x_311;
} else {
 lean_dec_ref(x_311);
 x_327 = lean_box(0);
}
if (lean_is_scalar(x_327)) {
 x_328 = lean_alloc_ctor(1, 2, 0);
} else {
 x_328 = x_327;
}
lean_ctor_set(x_328, 0, x_325);
lean_ctor_set(x_328, 1, x_326);
return x_328;
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_276);
lean_dec(x_273);
lean_free_object(x_268);
lean_free_object(x_261);
lean_free_object(x_257);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_329 = lean_ctor_get(x_308, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_308, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_331 = x_308;
} else {
 lean_dec_ref(x_308);
 x_331 = lean_box(0);
}
if (lean_is_scalar(x_331)) {
 x_332 = lean_alloc_ctor(1, 2, 0);
} else {
 x_332 = x_331;
}
lean_ctor_set(x_332, 0, x_329);
lean_ctor_set(x_332, 1, x_330);
return x_332;
}
}
}
else
{
uint8_t x_333; 
lean_dec(x_273);
lean_free_object(x_268);
lean_free_object(x_261);
lean_free_object(x_257);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_333 = !lean_is_exclusive(x_275);
if (x_333 == 0)
{
return x_275;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_275, 0);
x_335 = lean_ctor_get(x_275, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_275);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
return x_336;
}
}
}
else
{
uint8_t x_337; 
lean_free_object(x_268);
lean_free_object(x_261);
lean_free_object(x_257);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_337 = !lean_is_exclusive(x_272);
if (x_337 == 0)
{
return x_272;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_272, 0);
x_339 = lean_ctor_get(x_272, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_272);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
return x_340;
}
}
}
else
{
lean_object* x_341; lean_object* x_342; 
x_341 = lean_ctor_get(x_268, 1);
lean_inc(x_341);
lean_dec(x_268);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_3);
x_342 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_3, x_243, x_247, x_248, x_249, x_250, x_341);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_256);
x_345 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_256, x_243, x_247, x_248, x_249, x_250, x_344);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
x_348 = lean_st_ref_get(x_243, x_347);
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
lean_inc(x_3);
x_352 = l_Lean_Meta_Grind_Goal_getRoot(x_349, x_3, x_249, x_250, x_350);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec(x_352);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
x_355 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_353, x_243, x_247, x_248, x_249, x_250, x_354);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
x_358 = lean_mk_string_unchecked("", 0, 0);
x_359 = l_Lean_stringToMessageData(x_358);
lean_dec(x_358);
lean_inc(x_359);
if (lean_is_scalar(x_351)) {
 x_360 = lean_alloc_ctor(7, 2, 0);
} else {
 x_360 = x_351;
 lean_ctor_set_tag(x_360, 7);
}
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_343);
x_361 = lean_mk_string_unchecked(" new root ", 10, 10);
x_362 = l_Lean_stringToMessageData(x_361);
lean_dec(x_361);
x_363 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_363, 0, x_360);
lean_ctor_set(x_363, 1, x_362);
lean_ctor_set_tag(x_261, 7);
lean_ctor_set(x_261, 1, x_346);
lean_ctor_set(x_261, 0, x_363);
x_364 = lean_mk_string_unchecked(", ", 2, 2);
x_365 = l_Lean_stringToMessageData(x_364);
lean_dec(x_364);
lean_ctor_set_tag(x_257, 7);
lean_ctor_set(x_257, 1, x_365);
lean_ctor_set(x_257, 0, x_261);
x_366 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_366, 0, x_257);
lean_ctor_set(x_366, 1, x_356);
x_367 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_359);
x_368 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_237, x_367, x_247, x_248, x_249, x_250, x_357);
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
lean_dec(x_368);
x_164 = x_252;
x_165 = x_238;
x_166 = x_256;
x_167 = x_240;
x_168 = x_239;
x_169 = x_254;
x_170 = x_242;
x_171 = x_241;
x_172 = x_243;
x_173 = x_244;
x_174 = x_245;
x_175 = x_246;
x_176 = x_247;
x_177 = x_248;
x_178 = x_249;
x_179 = x_250;
x_180 = x_369;
goto block_234;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_351);
lean_dec(x_346);
lean_dec(x_343);
lean_free_object(x_261);
lean_free_object(x_257);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_370 = lean_ctor_get(x_355, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_355, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_372 = x_355;
} else {
 lean_dec_ref(x_355);
 x_372 = lean_box(0);
}
if (lean_is_scalar(x_372)) {
 x_373 = lean_alloc_ctor(1, 2, 0);
} else {
 x_373 = x_372;
}
lean_ctor_set(x_373, 0, x_370);
lean_ctor_set(x_373, 1, x_371);
return x_373;
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_351);
lean_dec(x_346);
lean_dec(x_343);
lean_free_object(x_261);
lean_free_object(x_257);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_374 = lean_ctor_get(x_352, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_352, 1);
lean_inc(x_375);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_376 = x_352;
} else {
 lean_dec_ref(x_352);
 x_376 = lean_box(0);
}
if (lean_is_scalar(x_376)) {
 x_377 = lean_alloc_ctor(1, 2, 0);
} else {
 x_377 = x_376;
}
lean_ctor_set(x_377, 0, x_374);
lean_ctor_set(x_377, 1, x_375);
return x_377;
}
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_343);
lean_free_object(x_261);
lean_free_object(x_257);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_378 = lean_ctor_get(x_345, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_345, 1);
lean_inc(x_379);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_380 = x_345;
} else {
 lean_dec_ref(x_345);
 x_380 = lean_box(0);
}
if (lean_is_scalar(x_380)) {
 x_381 = lean_alloc_ctor(1, 2, 0);
} else {
 x_381 = x_380;
}
lean_ctor_set(x_381, 0, x_378);
lean_ctor_set(x_381, 1, x_379);
return x_381;
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_free_object(x_261);
lean_free_object(x_257);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_382 = lean_ctor_get(x_342, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_342, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_384 = x_342;
} else {
 lean_dec_ref(x_342);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_384)) {
 x_385 = lean_alloc_ctor(1, 2, 0);
} else {
 x_385 = x_384;
}
lean_ctor_set(x_385, 0, x_382);
lean_ctor_set(x_385, 1, x_383);
return x_385;
}
}
}
else
{
lean_free_object(x_261);
lean_free_object(x_257);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_268;
}
}
else
{
lean_object* x_386; lean_object* x_387; 
x_386 = lean_ctor_get(x_261, 1);
lean_inc(x_386);
lean_dec(x_261);
x_387 = l_Lean_Meta_Grind_updateLastTag(x_243, x_244, x_245, x_246, x_247, x_248, x_249, x_250, x_386);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_388 = lean_ctor_get(x_387, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_389 = x_387;
} else {
 lean_dec_ref(x_387);
 x_389 = lean_box(0);
}
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_3);
x_390 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_3, x_243, x_247, x_248, x_249, x_250, x_388);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_256);
x_393 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_256, x_243, x_247, x_248, x_249, x_250, x_392);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
lean_dec(x_393);
x_396 = lean_st_ref_get(x_243, x_395);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_399 = x_396;
} else {
 lean_dec_ref(x_396);
 x_399 = lean_box(0);
}
lean_inc(x_3);
x_400 = l_Lean_Meta_Grind_Goal_getRoot(x_397, x_3, x_249, x_250, x_398);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_400, 1);
lean_inc(x_402);
lean_dec(x_400);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
x_403 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_401, x_243, x_247, x_248, x_249, x_250, x_402);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
lean_dec(x_403);
x_406 = lean_mk_string_unchecked("", 0, 0);
x_407 = l_Lean_stringToMessageData(x_406);
lean_dec(x_406);
lean_inc(x_407);
if (lean_is_scalar(x_399)) {
 x_408 = lean_alloc_ctor(7, 2, 0);
} else {
 x_408 = x_399;
 lean_ctor_set_tag(x_408, 7);
}
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_391);
x_409 = lean_mk_string_unchecked(" new root ", 10, 10);
x_410 = l_Lean_stringToMessageData(x_409);
lean_dec(x_409);
if (lean_is_scalar(x_389)) {
 x_411 = lean_alloc_ctor(7, 2, 0);
} else {
 x_411 = x_389;
 lean_ctor_set_tag(x_411, 7);
}
lean_ctor_set(x_411, 0, x_408);
lean_ctor_set(x_411, 1, x_410);
x_412 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_394);
x_413 = lean_mk_string_unchecked(", ", 2, 2);
x_414 = l_Lean_stringToMessageData(x_413);
lean_dec(x_413);
lean_ctor_set_tag(x_257, 7);
lean_ctor_set(x_257, 1, x_414);
lean_ctor_set(x_257, 0, x_412);
x_415 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_415, 0, x_257);
lean_ctor_set(x_415, 1, x_404);
x_416 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_407);
x_417 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_237, x_416, x_247, x_248, x_249, x_250, x_405);
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
lean_dec(x_417);
x_164 = x_252;
x_165 = x_238;
x_166 = x_256;
x_167 = x_240;
x_168 = x_239;
x_169 = x_254;
x_170 = x_242;
x_171 = x_241;
x_172 = x_243;
x_173 = x_244;
x_174 = x_245;
x_175 = x_246;
x_176 = x_247;
x_177 = x_248;
x_178 = x_249;
x_179 = x_250;
x_180 = x_418;
goto block_234;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_399);
lean_dec(x_394);
lean_dec(x_391);
lean_dec(x_389);
lean_free_object(x_257);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_419 = lean_ctor_get(x_403, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_403, 1);
lean_inc(x_420);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 x_421 = x_403;
} else {
 lean_dec_ref(x_403);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_421)) {
 x_422 = lean_alloc_ctor(1, 2, 0);
} else {
 x_422 = x_421;
}
lean_ctor_set(x_422, 0, x_419);
lean_ctor_set(x_422, 1, x_420);
return x_422;
}
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_399);
lean_dec(x_394);
lean_dec(x_391);
lean_dec(x_389);
lean_free_object(x_257);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_423 = lean_ctor_get(x_400, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_400, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 lean_ctor_release(x_400, 1);
 x_425 = x_400;
} else {
 lean_dec_ref(x_400);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(1, 2, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_423);
lean_ctor_set(x_426, 1, x_424);
return x_426;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
lean_dec(x_391);
lean_dec(x_389);
lean_free_object(x_257);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_427 = lean_ctor_get(x_393, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_393, 1);
lean_inc(x_428);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_429 = x_393;
} else {
 lean_dec_ref(x_393);
 x_429 = lean_box(0);
}
if (lean_is_scalar(x_429)) {
 x_430 = lean_alloc_ctor(1, 2, 0);
} else {
 x_430 = x_429;
}
lean_ctor_set(x_430, 0, x_427);
lean_ctor_set(x_430, 1, x_428);
return x_430;
}
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
lean_dec(x_389);
lean_free_object(x_257);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_431 = lean_ctor_get(x_390, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_390, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 x_433 = x_390;
} else {
 lean_dec_ref(x_390);
 x_433 = lean_box(0);
}
if (lean_is_scalar(x_433)) {
 x_434 = lean_alloc_ctor(1, 2, 0);
} else {
 x_434 = x_433;
}
lean_ctor_set(x_434, 0, x_431);
lean_ctor_set(x_434, 1, x_432);
return x_434;
}
}
else
{
lean_free_object(x_257);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_387;
}
}
}
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; 
x_435 = lean_ctor_get(x_257, 1);
lean_inc(x_435);
lean_dec(x_257);
lean_inc(x_237);
x_436 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_237, x_249, x_435);
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_unbox(x_437);
lean_dec(x_437);
if (x_438 == 0)
{
lean_object* x_439; 
lean_dec(x_237);
x_439 = lean_ctor_get(x_436, 1);
lean_inc(x_439);
lean_dec(x_436);
x_164 = x_252;
x_165 = x_238;
x_166 = x_256;
x_167 = x_240;
x_168 = x_239;
x_169 = x_254;
x_170 = x_242;
x_171 = x_241;
x_172 = x_243;
x_173 = x_244;
x_174 = x_245;
x_175 = x_246;
x_176 = x_247;
x_177 = x_248;
x_178 = x_249;
x_179 = x_250;
x_180 = x_439;
goto block_234;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_436, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 lean_ctor_release(x_436, 1);
 x_441 = x_436;
} else {
 lean_dec_ref(x_436);
 x_441 = lean_box(0);
}
x_442 = l_Lean_Meta_Grind_updateLastTag(x_243, x_244, x_245, x_246, x_247, x_248, x_249, x_250, x_440);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_ctor_get(x_442, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_444 = x_442;
} else {
 lean_dec_ref(x_442);
 x_444 = lean_box(0);
}
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_3);
x_445 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_3, x_243, x_247, x_248, x_249, x_250, x_443);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
lean_dec(x_445);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_256);
x_448 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_256, x_243, x_247, x_248, x_249, x_250, x_447);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_448, 1);
lean_inc(x_450);
lean_dec(x_448);
x_451 = lean_st_ref_get(x_243, x_450);
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_454 = x_451;
} else {
 lean_dec_ref(x_451);
 x_454 = lean_box(0);
}
lean_inc(x_3);
x_455 = l_Lean_Meta_Grind_Goal_getRoot(x_452, x_3, x_249, x_250, x_453);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
lean_dec(x_455);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
x_458 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_456, x_243, x_247, x_248, x_249, x_250, x_457);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
lean_dec(x_458);
x_461 = lean_mk_string_unchecked("", 0, 0);
x_462 = l_Lean_stringToMessageData(x_461);
lean_dec(x_461);
lean_inc(x_462);
if (lean_is_scalar(x_454)) {
 x_463 = lean_alloc_ctor(7, 2, 0);
} else {
 x_463 = x_454;
 lean_ctor_set_tag(x_463, 7);
}
lean_ctor_set(x_463, 0, x_462);
lean_ctor_set(x_463, 1, x_446);
x_464 = lean_mk_string_unchecked(" new root ", 10, 10);
x_465 = l_Lean_stringToMessageData(x_464);
lean_dec(x_464);
if (lean_is_scalar(x_444)) {
 x_466 = lean_alloc_ctor(7, 2, 0);
} else {
 x_466 = x_444;
 lean_ctor_set_tag(x_466, 7);
}
lean_ctor_set(x_466, 0, x_463);
lean_ctor_set(x_466, 1, x_465);
if (lean_is_scalar(x_441)) {
 x_467 = lean_alloc_ctor(7, 2, 0);
} else {
 x_467 = x_441;
 lean_ctor_set_tag(x_467, 7);
}
lean_ctor_set(x_467, 0, x_466);
lean_ctor_set(x_467, 1, x_449);
x_468 = lean_mk_string_unchecked(", ", 2, 2);
x_469 = l_Lean_stringToMessageData(x_468);
lean_dec(x_468);
x_470 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_470, 0, x_467);
lean_ctor_set(x_470, 1, x_469);
x_471 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_471, 0, x_470);
lean_ctor_set(x_471, 1, x_459);
x_472 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_472, 0, x_471);
lean_ctor_set(x_472, 1, x_462);
x_473 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_237, x_472, x_247, x_248, x_249, x_250, x_460);
x_474 = lean_ctor_get(x_473, 1);
lean_inc(x_474);
lean_dec(x_473);
x_164 = x_252;
x_165 = x_238;
x_166 = x_256;
x_167 = x_240;
x_168 = x_239;
x_169 = x_254;
x_170 = x_242;
x_171 = x_241;
x_172 = x_243;
x_173 = x_244;
x_174 = x_245;
x_175 = x_246;
x_176 = x_247;
x_177 = x_248;
x_178 = x_249;
x_179 = x_250;
x_180 = x_474;
goto block_234;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
lean_dec(x_454);
lean_dec(x_449);
lean_dec(x_446);
lean_dec(x_444);
lean_dec(x_441);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_475 = lean_ctor_get(x_458, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_458, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_477 = x_458;
} else {
 lean_dec_ref(x_458);
 x_477 = lean_box(0);
}
if (lean_is_scalar(x_477)) {
 x_478 = lean_alloc_ctor(1, 2, 0);
} else {
 x_478 = x_477;
}
lean_ctor_set(x_478, 0, x_475);
lean_ctor_set(x_478, 1, x_476);
return x_478;
}
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_dec(x_454);
lean_dec(x_449);
lean_dec(x_446);
lean_dec(x_444);
lean_dec(x_441);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_479 = lean_ctor_get(x_455, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_455, 1);
lean_inc(x_480);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 x_481 = x_455;
} else {
 lean_dec_ref(x_455);
 x_481 = lean_box(0);
}
if (lean_is_scalar(x_481)) {
 x_482 = lean_alloc_ctor(1, 2, 0);
} else {
 x_482 = x_481;
}
lean_ctor_set(x_482, 0, x_479);
lean_ctor_set(x_482, 1, x_480);
return x_482;
}
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
lean_dec(x_446);
lean_dec(x_444);
lean_dec(x_441);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_483 = lean_ctor_get(x_448, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_448, 1);
lean_inc(x_484);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 lean_ctor_release(x_448, 1);
 x_485 = x_448;
} else {
 lean_dec_ref(x_448);
 x_485 = lean_box(0);
}
if (lean_is_scalar(x_485)) {
 x_486 = lean_alloc_ctor(1, 2, 0);
} else {
 x_486 = x_485;
}
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_484);
return x_486;
}
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
lean_dec(x_444);
lean_dec(x_441);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_487 = lean_ctor_get(x_445, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_445, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_489 = x_445;
} else {
 lean_dec_ref(x_445);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(1, 2, 0);
} else {
 x_490 = x_489;
}
lean_ctor_set(x_490, 0, x_487);
lean_ctor_set(x_490, 1, x_488);
return x_490;
}
}
else
{
lean_dec(x_441);
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_442;
}
}
}
}
else
{
lean_dec(x_256);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_257;
}
}
else
{
uint8_t x_491; 
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_491 = !lean_is_exclusive(x_253);
if (x_491 == 0)
{
return x_253;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_ctor_get(x_253, 0);
x_493 = lean_ctor_get(x_253, 1);
lean_inc(x_493);
lean_inc(x_492);
lean_dec(x_253);
x_494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_494, 0, x_492);
lean_ctor_set(x_494, 1, x_493);
return x_494;
}
}
}
block_520:
{
uint8_t x_509; 
x_509 = l_Array_isEmpty___redArg(x_497);
if (x_509 == 0)
{
lean_object* x_510; lean_object* x_511; 
x_510 = lean_ctor_get(x_7, 0);
lean_inc(x_510);
lean_inc(x_507);
lean_inc(x_506);
lean_inc(x_505);
lean_inc(x_504);
lean_inc(x_503);
lean_inc(x_502);
lean_inc(x_501);
lean_inc(x_500);
x_511 = l_Lean_Meta_Grind_getFnRoots(x_510, x_500, x_501, x_502, x_503, x_504, x_505, x_506, x_507, x_508);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; 
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
lean_dec(x_511);
x_238 = x_496;
x_239 = x_497;
x_240 = x_499;
x_241 = x_498;
x_242 = x_512;
x_243 = x_500;
x_244 = x_501;
x_245 = x_502;
x_246 = x_503;
x_247 = x_504;
x_248 = x_505;
x_249 = x_506;
x_250 = x_507;
x_251 = x_513;
goto block_495;
}
else
{
uint8_t x_514; 
lean_dec(x_507);
lean_dec(x_506);
lean_dec(x_505);
lean_dec(x_504);
lean_dec(x_503);
lean_dec(x_502);
lean_dec(x_501);
lean_dec(x_500);
lean_dec(x_499);
lean_dec(x_498);
lean_dec(x_497);
lean_dec(x_496);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_514 = !lean_is_exclusive(x_511);
if (x_514 == 0)
{
return x_511;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_515 = lean_ctor_get(x_511, 0);
x_516 = lean_ctor_get(x_511, 1);
lean_inc(x_516);
lean_inc(x_515);
lean_dec(x_511);
x_517 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_517, 0, x_515);
lean_ctor_set(x_517, 1, x_516);
return x_517;
}
}
}
else
{
lean_object* x_518; lean_object* x_519; 
x_518 = lean_unsigned_to_nat(0u);
x_519 = lean_mk_empty_array_with_capacity(x_518);
x_238 = x_496;
x_239 = x_497;
x_240 = x_499;
x_241 = x_498;
x_242 = x_519;
x_243 = x_500;
x_244 = x_501;
x_245 = x_502;
x_246 = x_503;
x_247 = x_504;
x_248 = x_505;
x_249 = x_506;
x_250 = x_507;
x_251 = x_508;
goto block_495;
}
}
block_577:
{
lean_object* x_530; 
lean_inc(x_3);
x_530 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans(x_3, x_521, x_522, x_523, x_524, x_525, x_526, x_527, x_528, x_529);
if (lean_obj_tag(x_530) == 0)
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; uint8_t x_539; uint8_t x_540; uint8_t x_541; uint8_t x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_531 = lean_ctor_get(x_530, 1);
lean_inc(x_531);
lean_dec(x_530);
x_532 = lean_ctor_get(x_5, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_5, 1);
lean_inc(x_533);
x_534 = lean_ctor_get(x_5, 2);
lean_inc(x_534);
x_535 = lean_ctor_get(x_5, 3);
lean_inc(x_535);
x_536 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_536, 0, x_4);
x_537 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_537, 0, x_1);
x_538 = lean_ctor_get(x_5, 6);
lean_inc(x_538);
x_539 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_540 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 2);
x_541 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 3);
x_542 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 4);
x_543 = lean_ctor_get(x_5, 7);
lean_inc(x_543);
x_544 = lean_ctor_get(x_5, 8);
lean_inc(x_544);
x_545 = lean_ctor_get(x_5, 9);
lean_inc(x_545);
x_546 = lean_ctor_get(x_5, 10);
lean_inc(x_546);
x_547 = lean_ctor_get(x_5, 11);
lean_inc(x_547);
x_548 = lean_ctor_get(x_5, 12);
lean_inc(x_548);
lean_dec(x_5);
lean_inc(x_534);
x_549 = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(x_549, 0, x_532);
lean_ctor_set(x_549, 1, x_533);
lean_ctor_set(x_549, 2, x_534);
lean_ctor_set(x_549, 3, x_535);
lean_ctor_set(x_549, 4, x_536);
lean_ctor_set(x_549, 5, x_537);
lean_ctor_set(x_549, 6, x_538);
lean_ctor_set(x_549, 7, x_543);
lean_ctor_set(x_549, 8, x_544);
lean_ctor_set(x_549, 9, x_545);
lean_ctor_set(x_549, 10, x_546);
lean_ctor_set(x_549, 11, x_547);
lean_ctor_set(x_549, 12, x_548);
lean_ctor_set_uint8(x_549, sizeof(void*)*13, x_9);
lean_ctor_set_uint8(x_549, sizeof(void*)*13 + 1, x_539);
lean_ctor_set_uint8(x_549, sizeof(void*)*13 + 2, x_540);
lean_ctor_set_uint8(x_549, sizeof(void*)*13 + 3, x_541);
lean_ctor_set_uint8(x_549, sizeof(void*)*13 + 4, x_542);
lean_inc(x_3);
x_550 = l_Lean_Meta_Grind_setENode(x_3, x_549, x_521, x_522, x_523, x_524, x_525, x_526, x_527, x_528, x_531);
x_551 = lean_ctor_get(x_550, 1);
lean_inc(x_551);
lean_dec(x_550);
lean_inc(x_528);
lean_inc(x_527);
lean_inc(x_526);
lean_inc(x_525);
lean_inc(x_524);
lean_inc(x_523);
lean_inc(x_522);
lean_inc(x_521);
x_552 = l_Lean_Meta_Grind_getEqcLambdas(x_7, x_521, x_522, x_523, x_524, x_525, x_526, x_527, x_528, x_551);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_552, 1);
lean_inc(x_554);
lean_dec(x_552);
lean_inc(x_528);
lean_inc(x_527);
lean_inc(x_526);
lean_inc(x_525);
lean_inc(x_524);
lean_inc(x_523);
lean_inc(x_522);
lean_inc(x_521);
x_555 = l_Lean_Meta_Grind_getEqcLambdas(x_8, x_521, x_522, x_523, x_524, x_525, x_526, x_527, x_528, x_554);
if (lean_obj_tag(x_555) == 0)
{
lean_object* x_556; lean_object* x_557; uint8_t x_558; 
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_555, 1);
lean_inc(x_557);
lean_dec(x_555);
x_558 = l_Array_isEmpty___redArg(x_553);
if (x_558 == 0)
{
lean_object* x_559; lean_object* x_560; 
x_559 = lean_ctor_get(x_8, 0);
lean_inc(x_559);
lean_inc(x_528);
lean_inc(x_527);
lean_inc(x_526);
lean_inc(x_525);
lean_inc(x_524);
lean_inc(x_523);
lean_inc(x_522);
lean_inc(x_521);
x_560 = l_Lean_Meta_Grind_getFnRoots(x_559, x_521, x_522, x_523, x_524, x_525, x_526, x_527, x_528, x_557);
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_561; lean_object* x_562; 
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_560, 1);
lean_inc(x_562);
lean_dec(x_560);
x_496 = x_534;
x_497 = x_556;
x_498 = x_553;
x_499 = x_561;
x_500 = x_521;
x_501 = x_522;
x_502 = x_523;
x_503 = x_524;
x_504 = x_525;
x_505 = x_526;
x_506 = x_527;
x_507 = x_528;
x_508 = x_562;
goto block_520;
}
else
{
uint8_t x_563; 
lean_dec(x_556);
lean_dec(x_553);
lean_dec(x_534);
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_526);
lean_dec(x_525);
lean_dec(x_524);
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_521);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_563 = !lean_is_exclusive(x_560);
if (x_563 == 0)
{
return x_560;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_564 = lean_ctor_get(x_560, 0);
x_565 = lean_ctor_get(x_560, 1);
lean_inc(x_565);
lean_inc(x_564);
lean_dec(x_560);
x_566 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_566, 0, x_564);
lean_ctor_set(x_566, 1, x_565);
return x_566;
}
}
}
else
{
lean_object* x_567; lean_object* x_568; 
x_567 = lean_unsigned_to_nat(0u);
x_568 = lean_mk_empty_array_with_capacity(x_567);
x_496 = x_534;
x_497 = x_556;
x_498 = x_553;
x_499 = x_568;
x_500 = x_521;
x_501 = x_522;
x_502 = x_523;
x_503 = x_524;
x_504 = x_525;
x_505 = x_526;
x_506 = x_527;
x_507 = x_528;
x_508 = x_557;
goto block_520;
}
}
else
{
uint8_t x_569; 
lean_dec(x_553);
lean_dec(x_534);
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_526);
lean_dec(x_525);
lean_dec(x_524);
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_521);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_569 = !lean_is_exclusive(x_555);
if (x_569 == 0)
{
return x_555;
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_570 = lean_ctor_get(x_555, 0);
x_571 = lean_ctor_get(x_555, 1);
lean_inc(x_571);
lean_inc(x_570);
lean_dec(x_555);
x_572 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_572, 0, x_570);
lean_ctor_set(x_572, 1, x_571);
return x_572;
}
}
}
else
{
uint8_t x_573; 
lean_dec(x_534);
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_526);
lean_dec(x_525);
lean_dec(x_524);
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_521);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_573 = !lean_is_exclusive(x_552);
if (x_573 == 0)
{
return x_552;
}
else
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; 
x_574 = lean_ctor_get(x_552, 0);
x_575 = lean_ctor_get(x_552, 1);
lean_inc(x_575);
lean_inc(x_574);
lean_dec(x_552);
x_576 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_576, 0, x_574);
lean_ctor_set(x_576, 1, x_575);
return x_576;
}
}
}
else
{
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_526);
lean_dec(x_525);
lean_dec(x_524);
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_521);
lean_dec(x_237);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_530;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args) {
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
x_19 = lean_unbox(x_2);
lean_dec(x_2);
x_20 = lean_unbox(x_9);
lean_dec(x_9);
x_21 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(x_1, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_st_ref_get(x_5, x_13);
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
lean_inc(x_1);
x_22 = l_Lean_Meta_Grind_Goal_getENode(x_19, x_1, x_11, x_12, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_5, x_24);
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
lean_inc(x_2);
x_29 = l_Lean_Meta_Grind_Goal_getENode(x_26, x_2, x_11, x_12, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; uint8_t x_36; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_23, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 2);
lean_inc(x_33);
x_34 = lean_ptr_addr(x_32);
x_35 = lean_ptr_addr(x_33);
x_36 = lean_usize_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_178; uint8_t x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; uint8_t x_241; lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_262; lean_object* x_263; uint8_t x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; uint8_t x_275; lean_object* x_277; lean_object* x_278; uint8_t x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_290; lean_object* x_294; lean_object* x_295; uint8_t x_296; uint8_t x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_391; lean_object* x_392; uint8_t x_393; 
x_37 = lean_mk_string_unchecked("grind", 5, 5);
x_374 = lean_mk_string_unchecked("eqc", 3, 3);
lean_inc(x_37);
x_375 = l_Lean_Name_mkStr2(x_37, x_374);
lean_inc(x_375);
x_391 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_375, x_11, x_31);
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_unbox(x_392);
lean_dec(x_392);
if (x_393 == 0)
{
lean_object* x_394; 
lean_dec(x_375);
lean_dec(x_28);
lean_dec(x_21);
x_394 = lean_ctor_get(x_391, 1);
lean_inc(x_394);
lean_dec(x_391);
x_340 = x_5;
x_341 = x_6;
x_342 = x_7;
x_343 = x_8;
x_344 = x_9;
x_345 = x_10;
x_346 = x_11;
x_347 = x_12;
x_348 = x_394;
goto block_373;
}
else
{
lean_object* x_395; lean_object* x_396; 
x_395 = lean_ctor_get(x_391, 1);
lean_inc(x_395);
lean_dec(x_391);
x_396 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_395);
if (lean_obj_tag(x_396) == 0)
{
if (x_4 == 0)
{
lean_object* x_397; lean_object* x_398; 
x_397 = lean_ctor_get(x_396, 1);
lean_inc(x_397);
lean_dec(x_396);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_398 = l_Lean_Meta_mkEq(x_1, x_2, x_9, x_10, x_11, x_12, x_397);
x_376 = x_398;
goto block_390;
}
else
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_ctor_get(x_396, 1);
lean_inc(x_399);
lean_dec(x_396);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_400 = l_Lean_Meta_mkHEq(x_1, x_2, x_9, x_10, x_11, x_12, x_399);
x_376 = x_400;
goto block_390;
}
}
else
{
lean_dec(x_375);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_396;
}
}
block_115:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_mk_string_unchecked("debug", 5, 5);
x_48 = l_Lean_Name_mkStr2(x_37, x_47);
lean_inc(x_48);
x_49 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_48, x_44, x_46);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_48);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l_Lean_Meta_Grind_checkInvariants(x_36, x_38, x_39, x_40, x_41, x_42, x_43, x_44, x_45, x_52);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_dec(x_49);
x_55 = l_Lean_Meta_Grind_updateLastTag(x_38, x_39, x_40, x_41, x_42, x_43, x_44, x_45, x_54);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_55, 1);
x_58 = lean_ctor_get(x_55, 0);
lean_dec(x_58);
x_59 = lean_st_ref_get(x_38, x_57);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
x_63 = l_Lean_Meta_Grind_Goal_ppState(x_61, x_42, x_43, x_44, x_45, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_mk_string_unchecked("after addEqStep, ", 17, 17);
x_67 = l_Lean_stringToMessageData(x_66);
lean_dec(x_66);
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_64);
lean_ctor_set(x_59, 0, x_67);
x_68 = lean_mk_string_unchecked("", 0, 0);
x_69 = l_Lean_stringToMessageData(x_68);
lean_dec(x_68);
lean_ctor_set_tag(x_55, 7);
lean_ctor_set(x_55, 1, x_69);
lean_ctor_set(x_55, 0, x_59);
x_70 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_48, x_55, x_42, x_43, x_44, x_45, x_65);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Lean_Meta_Grind_checkInvariants(x_36, x_38, x_39, x_40, x_41, x_42, x_43, x_44, x_45, x_71);
return x_72;
}
else
{
uint8_t x_73; 
lean_free_object(x_59);
lean_free_object(x_55);
lean_dec(x_48);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
x_73 = !lean_is_exclusive(x_63);
if (x_73 == 0)
{
return x_63;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_63, 0);
x_75 = lean_ctor_get(x_63, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_63);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_59, 0);
x_78 = lean_ctor_get(x_59, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_59);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
x_79 = l_Lean_Meta_Grind_Goal_ppState(x_77, x_42, x_43, x_44, x_45, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_mk_string_unchecked("after addEqStep, ", 17, 17);
x_83 = l_Lean_stringToMessageData(x_82);
lean_dec(x_82);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
x_85 = lean_mk_string_unchecked("", 0, 0);
x_86 = l_Lean_stringToMessageData(x_85);
lean_dec(x_85);
lean_ctor_set_tag(x_55, 7);
lean_ctor_set(x_55, 1, x_86);
lean_ctor_set(x_55, 0, x_84);
x_87 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_48, x_55, x_42, x_43, x_44, x_45, x_81);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = l_Lean_Meta_Grind_checkInvariants(x_36, x_38, x_39, x_40, x_41, x_42, x_43, x_44, x_45, x_88);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_free_object(x_55);
lean_dec(x_48);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
x_90 = lean_ctor_get(x_79, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_79, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_92 = x_79;
} else {
 lean_dec_ref(x_79);
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
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_55, 1);
lean_inc(x_94);
lean_dec(x_55);
x_95 = lean_st_ref_get(x_38, x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
x_99 = l_Lean_Meta_Grind_Goal_ppState(x_96, x_42, x_43, x_44, x_45, x_97);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_mk_string_unchecked("after addEqStep, ", 17, 17);
x_103 = l_Lean_stringToMessageData(x_102);
lean_dec(x_102);
if (lean_is_scalar(x_98)) {
 x_104 = lean_alloc_ctor(7, 2, 0);
} else {
 x_104 = x_98;
 lean_ctor_set_tag(x_104, 7);
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_100);
x_105 = lean_mk_string_unchecked("", 0, 0);
x_106 = l_Lean_stringToMessageData(x_105);
lean_dec(x_105);
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_48, x_107, x_42, x_43, x_44, x_45, x_101);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_110 = l_Lean_Meta_Grind_checkInvariants(x_36, x_38, x_39, x_40, x_41, x_42, x_43, x_44, x_45, x_109);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_98);
lean_dec(x_48);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
x_111 = lean_ctor_get(x_99, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_99, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_113 = x_99;
} else {
 lean_dec_ref(x_99);
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
else
{
lean_dec(x_48);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
return x_55;
}
}
}
block_138:
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_128 = l_Lean_Meta_Grind_isInconsistent___redArg(x_119, x_127);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_unbox(x_129);
lean_dec(x_129);
if (x_130 == 0)
{
if (x_117 == 0)
{
lean_object* x_131; 
lean_dec(x_118);
lean_dec(x_116);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_38 = x_119;
x_39 = x_120;
x_40 = x_121;
x_41 = x_122;
x_42 = x_123;
x_43 = x_124;
x_44 = x_125;
x_45 = x_126;
x_46 = x_131;
goto block_115;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
lean_dec(x_128);
x_133 = lean_ctor_get(x_116, 0);
lean_inc(x_133);
lean_dec(x_116);
x_134 = lean_ctor_get(x_118, 0);
lean_inc(x_134);
lean_dec(x_118);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
x_135 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(x_133, x_134, x_119, x_120, x_121, x_122, x_123, x_124, x_125, x_126, x_132);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_38 = x_119;
x_39 = x_120;
x_40 = x_121;
x_41 = x_122;
x_42 = x_123;
x_43 = x_124;
x_44 = x_125;
x_45 = x_126;
x_46 = x_136;
goto block_115;
}
else
{
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_37);
return x_135;
}
}
}
else
{
lean_object* x_137; 
lean_dec(x_118);
lean_dec(x_116);
x_137 = lean_ctor_get(x_128, 1);
lean_inc(x_137);
lean_dec(x_128);
x_38 = x_119;
x_39 = x_120;
x_40 = x_121;
x_41 = x_122;
x_42 = x_123;
x_43 = x_124;
x_44 = x_125;
x_45 = x_126;
x_46 = x_137;
goto block_115;
}
}
block_156:
{
if (x_151 == 0)
{
x_116 = x_142;
x_117 = x_147;
x_118 = x_149;
x_119 = x_140;
x_120 = x_150;
x_121 = x_139;
x_122 = x_141;
x_123 = x_145;
x_124 = x_144;
x_125 = x_148;
x_126 = x_143;
x_127 = x_146;
goto block_138;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_142, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_149, 0);
lean_inc(x_153);
lean_inc(x_143);
lean_inc(x_148);
lean_inc(x_144);
lean_inc(x_145);
lean_inc(x_141);
lean_inc(x_139);
lean_inc(x_150);
lean_inc(x_140);
x_154 = l_Lean_Meta_Grind_propagateCtor(x_152, x_153, x_140, x_150, x_139, x_141, x_145, x_144, x_148, x_143, x_146);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_116 = x_142;
x_117 = x_147;
x_118 = x_149;
x_119 = x_140;
x_120 = x_150;
x_121 = x_139;
x_122 = x_141;
x_123 = x_145;
x_124 = x_144;
x_125 = x_148;
x_126 = x_143;
x_127 = x_155;
goto block_138;
}
else
{
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_37);
return x_154;
}
}
}
block_177:
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = l_Lean_Meta_Grind_isInconsistent___redArg(x_160, x_168);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_unbox(x_170);
lean_dec(x_170);
if (x_171 == 0)
{
uint8_t x_172; 
x_172 = lean_ctor_get_uint8(x_157, sizeof(void*)*13 + 2);
if (x_172 == 0)
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_169, 1);
lean_inc(x_173);
lean_dec(x_169);
x_139 = x_162;
x_140 = x_160;
x_141 = x_163;
x_142 = x_157;
x_143 = x_167;
x_144 = x_165;
x_145 = x_164;
x_146 = x_173;
x_147 = x_158;
x_148 = x_166;
x_149 = x_159;
x_150 = x_161;
x_151 = x_36;
goto block_156;
}
else
{
lean_object* x_174; uint8_t x_175; 
x_174 = lean_ctor_get(x_169, 1);
lean_inc(x_174);
lean_dec(x_169);
x_175 = lean_ctor_get_uint8(x_159, sizeof(void*)*13 + 2);
x_139 = x_162;
x_140 = x_160;
x_141 = x_163;
x_142 = x_157;
x_143 = x_167;
x_144 = x_165;
x_145 = x_164;
x_146 = x_174;
x_147 = x_158;
x_148 = x_166;
x_149 = x_159;
x_150 = x_161;
x_151 = x_175;
goto block_156;
}
}
else
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_169, 1);
lean_inc(x_176);
lean_dec(x_169);
x_116 = x_157;
x_117 = x_158;
x_118 = x_159;
x_119 = x_160;
x_120 = x_161;
x_121 = x_162;
x_122 = x_163;
x_123 = x_164;
x_124 = x_165;
x_125 = x_166;
x_126 = x_167;
x_127 = x_176;
goto block_138;
}
}
block_193:
{
if (x_181 == 0)
{
x_157 = x_178;
x_158 = x_179;
x_159 = x_180;
x_160 = x_182;
x_161 = x_183;
x_162 = x_184;
x_163 = x_185;
x_164 = x_186;
x_165 = x_187;
x_166 = x_188;
x_167 = x_189;
x_168 = x_190;
goto block_177;
}
else
{
lean_object* x_191; 
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
x_191 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(x_182, x_183, x_184, x_185, x_186, x_187, x_188, x_189, x_190);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_157 = x_178;
x_158 = x_179;
x_159 = x_180;
x_160 = x_182;
x_161 = x_183;
x_162 = x_184;
x_163 = x_185;
x_164 = x_186;
x_165 = x_187;
x_166 = x_188;
x_167 = x_189;
x_168 = x_192;
goto block_177;
}
else
{
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_180);
lean_dec(x_178);
lean_dec(x_37);
return x_191;
}
}
}
block_211:
{
lean_object* x_207; uint8_t x_208; lean_object* x_209; 
x_207 = lean_box(1);
x_208 = lean_unbox(x_207);
lean_inc(x_195);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_202);
lean_inc(x_200);
lean_inc(x_194);
lean_inc(x_198);
lean_inc(x_203);
lean_inc(x_201);
lean_inc(x_197);
x_209 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(x_3, x_4, x_2, x_1, x_30, x_23, x_197, x_201, x_208, x_203, x_198, x_194, x_200, x_202, x_204, x_205, x_195, x_199);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
lean_dec(x_209);
x_178 = x_201;
x_179 = x_196;
x_180 = x_197;
x_181 = x_206;
x_182 = x_203;
x_183 = x_198;
x_184 = x_194;
x_185 = x_200;
x_186 = x_202;
x_187 = x_204;
x_188 = x_205;
x_189 = x_195;
x_190 = x_210;
goto block_193;
}
else
{
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_37);
return x_209;
}
}
block_227:
{
lean_object* x_225; 
lean_inc(x_213);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_220);
lean_inc(x_218);
lean_inc(x_212);
lean_inc(x_216);
lean_inc(x_221);
lean_inc(x_215);
lean_inc(x_219);
x_225 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(x_3, x_4, x_1, x_2, x_23, x_30, x_219, x_215, x_36, x_221, x_216, x_212, x_218, x_220, x_222, x_223, x_213, x_217);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
lean_dec(x_225);
x_178 = x_219;
x_179 = x_214;
x_180 = x_215;
x_181 = x_224;
x_182 = x_221;
x_183 = x_216;
x_184 = x_212;
x_185 = x_218;
x_186 = x_220;
x_187 = x_222;
x_188 = x_223;
x_189 = x_213;
x_190 = x_226;
goto block_193;
}
else
{
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_37);
return x_225;
}
}
block_242:
{
if (x_241 == 0)
{
x_212 = x_228;
x_213 = x_229;
x_214 = x_230;
x_215 = x_231;
x_216 = x_232;
x_217 = x_233;
x_218 = x_234;
x_219 = x_235;
x_220 = x_236;
x_221 = x_237;
x_222 = x_238;
x_223 = x_239;
x_224 = x_240;
goto block_227;
}
else
{
x_194 = x_228;
x_195 = x_229;
x_196 = x_230;
x_197 = x_231;
x_198 = x_232;
x_199 = x_233;
x_200 = x_234;
x_201 = x_235;
x_202 = x_236;
x_203 = x_237;
x_204 = x_238;
x_205 = x_239;
x_206 = x_240;
goto block_211;
}
}
block_261:
{
lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_256 = lean_ctor_get(x_246, 6);
lean_inc(x_256);
x_257 = lean_ctor_get(x_250, 6);
lean_inc(x_257);
x_258 = lean_nat_dec_lt(x_256, x_257);
lean_dec(x_257);
lean_dec(x_256);
if (x_258 == 0)
{
x_228 = x_243;
x_229 = x_244;
x_230 = x_245;
x_231 = x_246;
x_232 = x_247;
x_233 = x_248;
x_234 = x_249;
x_235 = x_250;
x_236 = x_251;
x_237 = x_252;
x_238 = x_253;
x_239 = x_254;
x_240 = x_255;
x_241 = x_36;
goto block_242;
}
else
{
uint8_t x_259; 
x_259 = lean_ctor_get_uint8(x_246, sizeof(void*)*13 + 1);
if (x_259 == 0)
{
if (x_258 == 0)
{
x_228 = x_243;
x_229 = x_244;
x_230 = x_245;
x_231 = x_246;
x_232 = x_247;
x_233 = x_248;
x_234 = x_249;
x_235 = x_250;
x_236 = x_251;
x_237 = x_252;
x_238 = x_253;
x_239 = x_254;
x_240 = x_255;
x_241 = x_36;
goto block_242;
}
else
{
uint8_t x_260; 
x_260 = lean_ctor_get_uint8(x_246, sizeof(void*)*13 + 2);
if (x_260 == 0)
{
x_228 = x_243;
x_229 = x_244;
x_230 = x_245;
x_231 = x_246;
x_232 = x_247;
x_233 = x_248;
x_234 = x_249;
x_235 = x_250;
x_236 = x_251;
x_237 = x_252;
x_238 = x_253;
x_239 = x_254;
x_240 = x_255;
x_241 = x_258;
goto block_242;
}
else
{
x_212 = x_243;
x_213 = x_244;
x_214 = x_245;
x_215 = x_246;
x_216 = x_247;
x_217 = x_248;
x_218 = x_249;
x_219 = x_250;
x_220 = x_251;
x_221 = x_252;
x_222 = x_253;
x_223 = x_254;
x_224 = x_255;
goto block_227;
}
}
}
else
{
x_228 = x_243;
x_229 = x_244;
x_230 = x_245;
x_231 = x_246;
x_232 = x_247;
x_233 = x_248;
x_234 = x_249;
x_235 = x_250;
x_236 = x_251;
x_237 = x_252;
x_238 = x_253;
x_239 = x_254;
x_240 = x_255;
x_241 = x_36;
goto block_242;
}
}
}
block_276:
{
if (x_275 == 0)
{
x_243 = x_262;
x_244 = x_263;
x_245 = x_264;
x_246 = x_265;
x_247 = x_266;
x_248 = x_267;
x_249 = x_268;
x_250 = x_269;
x_251 = x_270;
x_252 = x_271;
x_253 = x_272;
x_254 = x_273;
x_255 = x_274;
goto block_261;
}
else
{
x_194 = x_262;
x_195 = x_263;
x_196 = x_264;
x_197 = x_265;
x_198 = x_266;
x_199 = x_267;
x_200 = x_268;
x_201 = x_269;
x_202 = x_270;
x_203 = x_271;
x_204 = x_272;
x_205 = x_273;
x_206 = x_274;
goto block_211;
}
}
block_293:
{
if (x_290 == 0)
{
uint8_t x_291; 
x_291 = lean_ctor_get_uint8(x_284, sizeof(void*)*13 + 2);
if (x_291 == 0)
{
x_262 = x_277;
x_263 = x_278;
x_264 = x_279;
x_265 = x_280;
x_266 = x_281;
x_267 = x_282;
x_268 = x_283;
x_269 = x_284;
x_270 = x_285;
x_271 = x_286;
x_272 = x_287;
x_273 = x_288;
x_274 = x_289;
x_275 = x_36;
goto block_276;
}
else
{
uint8_t x_292; 
x_292 = lean_ctor_get_uint8(x_280, sizeof(void*)*13 + 2);
if (x_292 == 0)
{
x_262 = x_277;
x_263 = x_278;
x_264 = x_279;
x_265 = x_280;
x_266 = x_281;
x_267 = x_282;
x_268 = x_283;
x_269 = x_284;
x_270 = x_285;
x_271 = x_286;
x_272 = x_287;
x_273 = x_288;
x_274 = x_289;
x_275 = x_291;
goto block_276;
}
else
{
x_243 = x_277;
x_244 = x_278;
x_245 = x_279;
x_246 = x_280;
x_247 = x_281;
x_248 = x_282;
x_249 = x_283;
x_250 = x_284;
x_251 = x_285;
x_252 = x_286;
x_253 = x_287;
x_254 = x_288;
x_255 = x_289;
goto block_261;
}
}
}
else
{
x_194 = x_277;
x_195 = x_278;
x_196 = x_279;
x_197 = x_280;
x_198 = x_281;
x_199 = x_282;
x_200 = x_283;
x_201 = x_284;
x_202 = x_285;
x_203 = x_286;
x_204 = x_287;
x_205 = x_288;
x_206 = x_289;
goto block_211;
}
}
block_309:
{
uint8_t x_307; 
x_307 = lean_ctor_get_uint8(x_294, sizeof(void*)*13 + 1);
if (x_307 == 0)
{
x_277 = x_300;
x_278 = x_305;
x_279 = x_297;
x_280 = x_295;
x_281 = x_299;
x_282 = x_306;
x_283 = x_301;
x_284 = x_294;
x_285 = x_302;
x_286 = x_298;
x_287 = x_303;
x_288 = x_304;
x_289 = x_296;
x_290 = x_36;
goto block_293;
}
else
{
uint8_t x_308; 
x_308 = lean_ctor_get_uint8(x_295, sizeof(void*)*13 + 1);
if (x_308 == 0)
{
x_277 = x_300;
x_278 = x_305;
x_279 = x_297;
x_280 = x_295;
x_281 = x_299;
x_282 = x_306;
x_283 = x_301;
x_284 = x_294;
x_285 = x_302;
x_286 = x_298;
x_287 = x_303;
x_288 = x_304;
x_289 = x_296;
x_290 = x_307;
goto block_293;
}
else
{
x_277 = x_300;
x_278 = x_305;
x_279 = x_297;
x_280 = x_295;
x_281 = x_299;
x_282 = x_306;
x_283 = x_301;
x_284 = x_294;
x_285 = x_302;
x_286 = x_298;
x_287 = x_303;
x_288 = x_304;
x_289 = x_296;
x_290 = x_36;
goto block_293;
}
}
}
block_324:
{
lean_object* x_322; 
x_322 = l_Lean_Meta_Grind_markAsInconsistent(x_316, x_310, x_315, x_314, x_320, x_313, x_318, x_312, x_317);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; 
x_323 = lean_ctor_get(x_322, 1);
lean_inc(x_323);
lean_dec(x_322);
x_294 = x_311;
x_295 = x_319;
x_296 = x_321;
x_297 = x_36;
x_298 = x_316;
x_299 = x_310;
x_300 = x_315;
x_301 = x_314;
x_302 = x_320;
x_303 = x_313;
x_304 = x_318;
x_305 = x_312;
x_306 = x_323;
goto block_309;
}
else
{
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_312);
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_37);
lean_dec(x_30);
lean_dec(x_23);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_322;
}
}
block_339:
{
if (x_336 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
x_294 = x_326;
x_295 = x_334;
x_296 = x_36;
x_297 = x_36;
x_298 = x_331;
x_299 = x_325;
x_300 = x_330;
x_301 = x_329;
x_302 = x_335;
x_303 = x_328;
x_304 = x_333;
x_305 = x_327;
x_306 = x_332;
goto block_309;
}
else
{
uint8_t x_337; 
x_337 = l_Lean_Expr_isTrue(x_32);
if (x_337 == 0)
{
uint8_t x_338; 
x_338 = l_Lean_Expr_isTrue(x_33);
if (x_338 == 0)
{
x_294 = x_326;
x_295 = x_334;
x_296 = x_36;
x_297 = x_336;
x_298 = x_331;
x_299 = x_325;
x_300 = x_330;
x_301 = x_329;
x_302 = x_335;
x_303 = x_328;
x_304 = x_333;
x_305 = x_327;
x_306 = x_332;
goto block_309;
}
else
{
x_310 = x_325;
x_311 = x_326;
x_312 = x_327;
x_313 = x_328;
x_314 = x_329;
x_315 = x_330;
x_316 = x_331;
x_317 = x_332;
x_318 = x_333;
x_319 = x_334;
x_320 = x_335;
x_321 = x_338;
goto block_324;
}
}
else
{
lean_dec(x_33);
x_310 = x_325;
x_311 = x_326;
x_312 = x_327;
x_313 = x_328;
x_314 = x_329;
x_315 = x_330;
x_316 = x_331;
x_317 = x_332;
x_318 = x_333;
x_319 = x_334;
x_320 = x_335;
x_321 = x_337;
goto block_324;
}
}
}
block_373:
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_349 = lean_st_ref_get(x_340, x_348);
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
lean_dec(x_349);
lean_inc(x_32);
x_352 = l_Lean_Meta_Grind_Goal_getENode(x_350, x_32, x_346, x_347, x_351);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec(x_352);
x_355 = lean_st_ref_get(x_340, x_354);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
lean_inc(x_33);
x_358 = l_Lean_Meta_Grind_Goal_getENode(x_356, x_33, x_346, x_347, x_357);
if (lean_obj_tag(x_358) == 0)
{
uint8_t x_359; 
x_359 = lean_ctor_get_uint8(x_353, sizeof(void*)*13 + 1);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; 
x_360 = lean_ctor_get(x_358, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_358, 1);
lean_inc(x_361);
lean_dec(x_358);
x_325 = x_341;
x_326 = x_353;
x_327 = x_347;
x_328 = x_345;
x_329 = x_343;
x_330 = x_342;
x_331 = x_340;
x_332 = x_361;
x_333 = x_346;
x_334 = x_360;
x_335 = x_344;
x_336 = x_36;
goto block_339;
}
else
{
lean_object* x_362; lean_object* x_363; uint8_t x_364; 
x_362 = lean_ctor_get(x_358, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_358, 1);
lean_inc(x_363);
lean_dec(x_358);
x_364 = lean_ctor_get_uint8(x_362, sizeof(void*)*13 + 1);
x_325 = x_341;
x_326 = x_353;
x_327 = x_347;
x_328 = x_345;
x_329 = x_343;
x_330 = x_342;
x_331 = x_340;
x_332 = x_363;
x_333 = x_346;
x_334 = x_362;
x_335 = x_344;
x_336 = x_364;
goto block_339;
}
}
else
{
uint8_t x_365; 
lean_dec(x_353);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_23);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_365 = !lean_is_exclusive(x_358);
if (x_365 == 0)
{
return x_358;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_366 = lean_ctor_get(x_358, 0);
x_367 = lean_ctor_get(x_358, 1);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_358);
x_368 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_368, 0, x_366);
lean_ctor_set(x_368, 1, x_367);
return x_368;
}
}
}
else
{
uint8_t x_369; 
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_23);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_369 = !lean_is_exclusive(x_352);
if (x_369 == 0)
{
return x_352;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = lean_ctor_get(x_352, 0);
x_371 = lean_ctor_get(x_352, 1);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_352);
x_372 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
return x_372;
}
}
}
block_390:
{
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
lean_dec(x_376);
x_379 = lean_mk_string_unchecked("", 0, 0);
x_380 = l_Lean_stringToMessageData(x_379);
lean_dec(x_379);
x_381 = l_Lean_MessageData_ofExpr(x_377);
lean_inc(x_380);
if (lean_is_scalar(x_28)) {
 x_382 = lean_alloc_ctor(7, 2, 0);
} else {
 x_382 = x_28;
 lean_ctor_set_tag(x_382, 7);
}
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
if (lean_is_scalar(x_21)) {
 x_383 = lean_alloc_ctor(7, 2, 0);
} else {
 x_383 = x_21;
 lean_ctor_set_tag(x_383, 7);
}
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_380);
x_384 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_375, x_383, x_9, x_10, x_11, x_12, x_378);
x_385 = lean_ctor_get(x_384, 1);
lean_inc(x_385);
lean_dec(x_384);
x_340 = x_5;
x_341 = x_6;
x_342 = x_7;
x_343 = x_8;
x_344 = x_9;
x_345 = x_10;
x_346 = x_11;
x_347 = x_12;
x_348 = x_385;
goto block_373;
}
else
{
uint8_t x_386; 
lean_dec(x_375);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_386 = !lean_is_exclusive(x_376);
if (x_386 == 0)
{
return x_376;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_376, 0);
x_388 = lean_ctor_get(x_376, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_376);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
return x_389;
}
}
}
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_23);
lean_dec(x_3);
x_401 = lean_mk_string_unchecked("grind", 5, 5);
x_402 = lean_mk_string_unchecked("debug", 5, 5);
x_403 = l_Lean_Name_mkStr2(x_401, x_402);
lean_inc(x_403);
x_404 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_403, x_11, x_31);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_unbox(x_405);
lean_dec(x_405);
if (x_406 == 0)
{
lean_object* x_407; 
lean_dec(x_403);
lean_dec(x_28);
lean_dec(x_21);
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
x_407 = lean_ctor_get(x_404, 1);
lean_inc(x_407);
lean_dec(x_404);
x_14 = x_407;
goto block_17;
}
else
{
uint8_t x_408; 
x_408 = !lean_is_exclusive(x_404);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_404, 1);
x_410 = lean_ctor_get(x_404, 0);
lean_dec(x_410);
x_411 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_409);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_411) == 0)
{
uint8_t x_412; 
x_412 = !lean_is_exclusive(x_411);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_413 = lean_ctor_get(x_411, 1);
x_414 = lean_ctor_get(x_411, 0);
lean_dec(x_414);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_415 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_1, x_5, x_9, x_10, x_11, x_12, x_413);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_415, 1);
lean_inc(x_417);
lean_dec(x_415);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_418 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_2, x_5, x_9, x_10, x_11, x_12, x_417);
lean_dec(x_5);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_418, 1);
lean_inc(x_420);
lean_dec(x_418);
x_421 = lean_mk_string_unchecked("", 0, 0);
x_422 = l_Lean_stringToMessageData(x_421);
lean_dec(x_421);
lean_ctor_set_tag(x_411, 7);
lean_ctor_set(x_411, 1, x_416);
lean_ctor_set(x_411, 0, x_422);
x_423 = lean_mk_string_unchecked(" and ", 5, 5);
x_424 = l_Lean_stringToMessageData(x_423);
lean_dec(x_423);
lean_ctor_set_tag(x_404, 7);
lean_ctor_set(x_404, 1, x_424);
lean_ctor_set(x_404, 0, x_411);
if (lean_is_scalar(x_28)) {
 x_425 = lean_alloc_ctor(7, 2, 0);
} else {
 x_425 = x_28;
 lean_ctor_set_tag(x_425, 7);
}
lean_ctor_set(x_425, 0, x_404);
lean_ctor_set(x_425, 1, x_419);
x_426 = lean_mk_string_unchecked(" are already in the same equivalence class", 42, 42);
x_427 = l_Lean_stringToMessageData(x_426);
lean_dec(x_426);
if (lean_is_scalar(x_21)) {
 x_428 = lean_alloc_ctor(7, 2, 0);
} else {
 x_428 = x_21;
 lean_ctor_set_tag(x_428, 7);
}
lean_ctor_set(x_428, 0, x_425);
lean_ctor_set(x_428, 1, x_427);
x_429 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_403, x_428, x_9, x_10, x_11, x_12, x_420);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_430 = lean_ctor_get(x_429, 1);
lean_inc(x_430);
lean_dec(x_429);
x_14 = x_430;
goto block_17;
}
else
{
uint8_t x_431; 
lean_dec(x_416);
lean_free_object(x_411);
lean_free_object(x_404);
lean_dec(x_403);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_431 = !lean_is_exclusive(x_418);
if (x_431 == 0)
{
return x_418;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_432 = lean_ctor_get(x_418, 0);
x_433 = lean_ctor_get(x_418, 1);
lean_inc(x_433);
lean_inc(x_432);
lean_dec(x_418);
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set(x_434, 1, x_433);
return x_434;
}
}
}
else
{
uint8_t x_435; 
lean_free_object(x_411);
lean_free_object(x_404);
lean_dec(x_403);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
x_435 = !lean_is_exclusive(x_415);
if (x_435 == 0)
{
return x_415;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_436 = lean_ctor_get(x_415, 0);
x_437 = lean_ctor_get(x_415, 1);
lean_inc(x_437);
lean_inc(x_436);
lean_dec(x_415);
x_438 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set(x_438, 1, x_437);
return x_438;
}
}
}
else
{
lean_object* x_439; lean_object* x_440; 
x_439 = lean_ctor_get(x_411, 1);
lean_inc(x_439);
lean_dec(x_411);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_440 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_1, x_5, x_9, x_10, x_11, x_12, x_439);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
lean_dec(x_440);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_443 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_2, x_5, x_9, x_10, x_11, x_12, x_442);
lean_dec(x_5);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
lean_dec(x_443);
x_446 = lean_mk_string_unchecked("", 0, 0);
x_447 = l_Lean_stringToMessageData(x_446);
lean_dec(x_446);
x_448 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_441);
x_449 = lean_mk_string_unchecked(" and ", 5, 5);
x_450 = l_Lean_stringToMessageData(x_449);
lean_dec(x_449);
lean_ctor_set_tag(x_404, 7);
lean_ctor_set(x_404, 1, x_450);
lean_ctor_set(x_404, 0, x_448);
if (lean_is_scalar(x_28)) {
 x_451 = lean_alloc_ctor(7, 2, 0);
} else {
 x_451 = x_28;
 lean_ctor_set_tag(x_451, 7);
}
lean_ctor_set(x_451, 0, x_404);
lean_ctor_set(x_451, 1, x_444);
x_452 = lean_mk_string_unchecked(" are already in the same equivalence class", 42, 42);
x_453 = l_Lean_stringToMessageData(x_452);
lean_dec(x_452);
if (lean_is_scalar(x_21)) {
 x_454 = lean_alloc_ctor(7, 2, 0);
} else {
 x_454 = x_21;
 lean_ctor_set_tag(x_454, 7);
}
lean_ctor_set(x_454, 0, x_451);
lean_ctor_set(x_454, 1, x_453);
x_455 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_403, x_454, x_9, x_10, x_11, x_12, x_445);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_456 = lean_ctor_get(x_455, 1);
lean_inc(x_456);
lean_dec(x_455);
x_14 = x_456;
goto block_17;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_441);
lean_free_object(x_404);
lean_dec(x_403);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_457 = lean_ctor_get(x_443, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_443, 1);
lean_inc(x_458);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 x_459 = x_443;
} else {
 lean_dec_ref(x_443);
 x_459 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(1, 2, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_457);
lean_ctor_set(x_460, 1, x_458);
return x_460;
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
lean_free_object(x_404);
lean_dec(x_403);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
x_461 = lean_ctor_get(x_440, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_440, 1);
lean_inc(x_462);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_463 = x_440;
} else {
 lean_dec_ref(x_440);
 x_463 = lean_box(0);
}
if (lean_is_scalar(x_463)) {
 x_464 = lean_alloc_ctor(1, 2, 0);
} else {
 x_464 = x_463;
}
lean_ctor_set(x_464, 0, x_461);
lean_ctor_set(x_464, 1, x_462);
return x_464;
}
}
}
else
{
lean_free_object(x_404);
lean_dec(x_403);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_411;
}
}
else
{
lean_object* x_465; lean_object* x_466; 
x_465 = lean_ctor_get(x_404, 1);
lean_inc(x_465);
lean_dec(x_404);
x_466 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_465);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_467 = lean_ctor_get(x_466, 1);
lean_inc(x_467);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_468 = x_466;
} else {
 lean_dec_ref(x_466);
 x_468 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_469 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_1, x_5, x_9, x_10, x_11, x_12, x_467);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
lean_dec(x_469);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_472 = l_Lean_Meta_Grind_ppENodeRef___redArg(x_2, x_5, x_9, x_10, x_11, x_12, x_471);
lean_dec(x_5);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_472, 1);
lean_inc(x_474);
lean_dec(x_472);
x_475 = lean_mk_string_unchecked("", 0, 0);
x_476 = l_Lean_stringToMessageData(x_475);
lean_dec(x_475);
if (lean_is_scalar(x_468)) {
 x_477 = lean_alloc_ctor(7, 2, 0);
} else {
 x_477 = x_468;
 lean_ctor_set_tag(x_477, 7);
}
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_470);
x_478 = lean_mk_string_unchecked(" and ", 5, 5);
x_479 = l_Lean_stringToMessageData(x_478);
lean_dec(x_478);
x_480 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_480, 0, x_477);
lean_ctor_set(x_480, 1, x_479);
if (lean_is_scalar(x_28)) {
 x_481 = lean_alloc_ctor(7, 2, 0);
} else {
 x_481 = x_28;
 lean_ctor_set_tag(x_481, 7);
}
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_473);
x_482 = lean_mk_string_unchecked(" are already in the same equivalence class", 42, 42);
x_483 = l_Lean_stringToMessageData(x_482);
lean_dec(x_482);
if (lean_is_scalar(x_21)) {
 x_484 = lean_alloc_ctor(7, 2, 0);
} else {
 x_484 = x_21;
 lean_ctor_set_tag(x_484, 7);
}
lean_ctor_set(x_484, 0, x_481);
lean_ctor_set(x_484, 1, x_483);
x_485 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_403, x_484, x_9, x_10, x_11, x_12, x_474);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_486 = lean_ctor_get(x_485, 1);
lean_inc(x_486);
lean_dec(x_485);
x_14 = x_486;
goto block_17;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
lean_dec(x_470);
lean_dec(x_468);
lean_dec(x_403);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_487 = lean_ctor_get(x_472, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_472, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 lean_ctor_release(x_472, 1);
 x_489 = x_472;
} else {
 lean_dec_ref(x_472);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(1, 2, 0);
} else {
 x_490 = x_489;
}
lean_ctor_set(x_490, 0, x_487);
lean_ctor_set(x_490, 1, x_488);
return x_490;
}
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_468);
lean_dec(x_403);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
x_491 = lean_ctor_get(x_469, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_469, 1);
lean_inc(x_492);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 lean_ctor_release(x_469, 1);
 x_493 = x_469;
} else {
 lean_dec_ref(x_469);
 x_493 = lean_box(0);
}
if (lean_is_scalar(x_493)) {
 x_494 = lean_alloc_ctor(1, 2, 0);
} else {
 x_494 = x_493;
}
lean_ctor_set(x_494, 0, x_491);
lean_ctor_set(x_494, 1, x_492);
return x_494;
}
}
else
{
lean_dec(x_403);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_466;
}
}
}
}
}
else
{
uint8_t x_495; 
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_495 = !lean_is_exclusive(x_29);
if (x_495 == 0)
{
return x_29;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_496 = lean_ctor_get(x_29, 0);
x_497 = lean_ctor_get(x_29, 1);
lean_inc(x_497);
lean_inc(x_496);
lean_dec(x_29);
x_498 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_498, 0, x_496);
lean_ctor_set(x_498, 1, x_497);
return x_498;
}
}
}
else
{
uint8_t x_499; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_499 = !lean_is_exclusive(x_22);
if (x_499 == 0)
{
return x_22;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_500 = lean_ctor_get(x_22, 0);
x_501 = lean_ctor_get(x_22, 1);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_22);
x_502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_502, 0, x_500);
lean_ctor_set(x_502, 1, x_501);
return x_502;
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 5);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 6);
lean_inc(x_12);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_mk_empty_array_with_capacity(x_13);
x_15 = lean_ctor_get_uint8(x_4, sizeof(void*)*16);
x_16 = lean_ctor_get(x_4, 8);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 9);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 10);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 11);
lean_inc(x_19);
x_20 = lean_ctor_get(x_4, 12);
lean_inc(x_20);
x_21 = lean_ctor_get(x_4, 13);
lean_inc(x_21);
x_22 = lean_ctor_get(x_4, 14);
lean_inc(x_22);
x_23 = lean_ctor_get(x_4, 15);
lean_inc(x_23);
lean_dec(x_4);
x_24 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_7);
lean_ctor_set(x_24, 2, x_8);
lean_ctor_set(x_24, 3, x_9);
lean_ctor_set(x_24, 4, x_10);
lean_ctor_set(x_24, 5, x_11);
lean_ctor_set(x_24, 6, x_12);
lean_ctor_set(x_24, 7, x_14);
lean_ctor_set(x_24, 8, x_16);
lean_ctor_set(x_24, 9, x_17);
lean_ctor_set(x_24, 10, x_18);
lean_ctor_set(x_24, 11, x_19);
lean_ctor_set(x_24, 12, x_20);
lean_ctor_set(x_24, 13, x_21);
lean_ctor_set(x_24, 14, x_22);
lean_ctor_set(x_24, 15, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*16, x_15);
x_25 = lean_st_ref_set(x_1, x_24, x_5);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(x_1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_5, 7);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Array_back_x3f(lean_box(0), x_7);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_free_object(x_3);
x_9 = lean_st_ref_take(x_1, x_6);
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
x_15 = lean_ctor_get(x_10, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 5);
lean_inc(x_17);
x_18 = lean_ctor_get(x_10, 6);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 7);
lean_inc(x_19);
x_20 = lean_array_pop(x_19);
x_21 = lean_ctor_get_uint8(x_10, sizeof(void*)*16);
x_22 = lean_ctor_get(x_10, 8);
lean_inc(x_22);
x_23 = lean_ctor_get(x_10, 9);
lean_inc(x_23);
x_24 = lean_ctor_get(x_10, 10);
lean_inc(x_24);
x_25 = lean_ctor_get(x_10, 11);
lean_inc(x_25);
x_26 = lean_ctor_get(x_10, 12);
lean_inc(x_26);
x_27 = lean_ctor_get(x_10, 13);
lean_inc(x_27);
x_28 = lean_ctor_get(x_10, 14);
lean_inc(x_28);
x_29 = lean_ctor_get(x_10, 15);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_13);
lean_ctor_set(x_30, 2, x_14);
lean_ctor_set(x_30, 3, x_15);
lean_ctor_set(x_30, 4, x_16);
lean_ctor_set(x_30, 5, x_17);
lean_ctor_set(x_30, 6, x_18);
lean_ctor_set(x_30, 7, x_20);
lean_ctor_set(x_30, 8, x_22);
lean_ctor_set(x_30, 9, x_23);
lean_ctor_set(x_30, 10, x_24);
lean_ctor_set(x_30, 11, x_25);
lean_ctor_set(x_30, 12, x_26);
lean_ctor_set(x_30, 13, x_27);
lean_ctor_set(x_30, 14, x_28);
lean_ctor_set(x_30, 15, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*16, x_21);
x_31 = lean_st_ref_set(x_1, x_30, x_11);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_8);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_3, 0);
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_3);
x_38 = lean_ctor_get(x_36, 7);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_back_x3f(lean_box(0), x_38);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_41 = lean_st_ref_take(x_1, x_37);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_42, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_42, 4);
lean_inc(x_48);
x_49 = lean_ctor_get(x_42, 5);
lean_inc(x_49);
x_50 = lean_ctor_get(x_42, 6);
lean_inc(x_50);
x_51 = lean_ctor_get(x_42, 7);
lean_inc(x_51);
x_52 = lean_array_pop(x_51);
x_53 = lean_ctor_get_uint8(x_42, sizeof(void*)*16);
x_54 = lean_ctor_get(x_42, 8);
lean_inc(x_54);
x_55 = lean_ctor_get(x_42, 9);
lean_inc(x_55);
x_56 = lean_ctor_get(x_42, 10);
lean_inc(x_56);
x_57 = lean_ctor_get(x_42, 11);
lean_inc(x_57);
x_58 = lean_ctor_get(x_42, 12);
lean_inc(x_58);
x_59 = lean_ctor_get(x_42, 13);
lean_inc(x_59);
x_60 = lean_ctor_get(x_42, 14);
lean_inc(x_60);
x_61 = lean_ctor_get(x_42, 15);
lean_inc(x_61);
lean_dec(x_42);
x_62 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_62, 0, x_44);
lean_ctor_set(x_62, 1, x_45);
lean_ctor_set(x_62, 2, x_46);
lean_ctor_set(x_62, 3, x_47);
lean_ctor_set(x_62, 4, x_48);
lean_ctor_set(x_62, 5, x_49);
lean_ctor_set(x_62, 6, x_50);
lean_ctor_set(x_62, 7, x_52);
lean_ctor_set(x_62, 8, x_54);
lean_ctor_set(x_62, 9, x_55);
lean_ctor_set(x_62, 10, x_56);
lean_ctor_set(x_62, 11, x_57);
lean_ctor_set(x_62, 12, x_58);
lean_ctor_set(x_62, 13, x_59);
lean_ctor_set(x_62, 14, x_60);
lean_ctor_set(x_62, 15, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*16, x_53);
x_63 = lean_st_ref_set(x_1, x_62, x_43);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_39);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(x_1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_grind_process_new_facts(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_15);
return x_16;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(x_1, x_2, x_3, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_box(1);
x_14 = lean_unbox(x_13);
x_15 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(x_1, x_2, x_3, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 5);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 6);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 7);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_5, sizeof(void*)*16);
x_16 = lean_ctor_get(x_5, 8);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 9);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 10);
lean_inc(x_18);
x_19 = l_Lean_PersistentArray_push___redArg(x_18, x_1);
x_20 = lean_ctor_get(x_5, 11);
lean_inc(x_20);
x_21 = lean_ctor_get(x_5, 12);
lean_inc(x_21);
x_22 = lean_ctor_get(x_5, 13);
lean_inc(x_22);
x_23 = lean_ctor_get(x_5, 14);
lean_inc(x_23);
x_24 = lean_ctor_get(x_5, 15);
lean_inc(x_24);
lean_dec(x_5);
x_25 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_8);
lean_ctor_set(x_25, 2, x_9);
lean_ctor_set(x_25, 3, x_10);
lean_ctor_set(x_25, 4, x_11);
lean_ctor_set(x_25, 5, x_12);
lean_ctor_set(x_25, 6, x_13);
lean_ctor_set(x_25, 7, x_14);
lean_ctor_set(x_25, 8, x_16);
lean_ctor_set(x_25, 9, x_17);
lean_ctor_set(x_25, 10, x_19);
lean_ctor_set(x_25, 11, x_20);
lean_ctor_set(x_25, 12, x_21);
lean_ctor_set(x_25, 13, x_22);
lean_ctor_set(x_25, 14, x_23);
lean_ctor_set(x_25, 15, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*16, x_15);
x_26 = lean_st_ref_set(x_2, x_25, x_6);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(x_1, x_2, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_Meta_mkEq(x_1, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_15);
x_17 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(x_15, x_5, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_19);
lean_inc(x_4);
lean_inc(x_1);
x_20 = lean_grind_internalize(x_1, x_4, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_22 = lean_grind_internalize(x_2, x_4, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_23);
return x_24;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_22;
}
}
else
{
lean_dec(x_19);
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
lean_dec(x_1);
return x_20;
}
}
else
{
uint8_t x_25; 
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
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_15 = lean_grind_internalize(x_3, x_2, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
if (x_4 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Meta_Grind_getTrueExpr(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_20 = l_Lean_Meta_mkEqTrue(x_1, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(x_3, x_18, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_dec(x_15);
x_29 = l_Lean_Meta_Grind_getFalseExpr(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_32 = l_Lean_Meta_mkEqFalse(x_1, x_9, x_10, x_11, x_12, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(x_3, x_30, x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_34);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (x_6 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_17);
lean_inc(x_2);
lean_inc(x_4);
x_18 = lean_grind_internalize(x_4, x_2, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
x_20 = lean_grind_internalize(x_5, x_2, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_21);
return x_22;
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_20;
}
}
else
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
lean_dec(x_4);
x_23 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_24 = lean_grind_internalize(x_3, x_2, x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Meta_Grind_getFalseExpr(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_29 = l_Lean_Meta_mkEqFalse(x_1, x_12, x_13, x_14, x_15, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(x_3, x_27, x_30, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_31);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = lean_unbox(x_7);
lean_dec(x_7);
x_19 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(x_1, x_2, x_3, x_4, x_5, x_17, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_inc(x_3);
x_14 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_3, x_10, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_cleanupAnnotations(x_15);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
x_19 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_inc(x_17);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_17);
x_22 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; 
lean_inc(x_20);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
x_25 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_29 = lean_mk_string_unchecked("Eq", 2, 2);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = l_Lean_Expr_isConstOf(x_28, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_20);
x_32 = l_Lean_Expr_isApp(x_28);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_33 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_35 = lean_mk_string_unchecked("HEq", 3, 3);
x_36 = l_Lean_Name_mkStr1(x_35);
x_37 = l_Lean_Expr_isConstOf(x_34, x_36);
lean_dec(x_36);
lean_dec(x_34);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_27);
lean_dec(x_26);
x_38 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(x_1, x_2, x_3, x_27, x_26, x_4, x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_28);
x_40 = l_Lean_Expr_isProp(x_27);
lean_dec(x_27);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_20, 1);
lean_inc(x_41);
lean_dec(x_20);
x_42 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(x_1, x_2, x_3, x_41, x_26, x_4, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_42;
}
else
{
lean_object* x_43; 
lean_dec(x_26);
lean_dec(x_20);
x_43 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_43;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_inc(x_1);
x_44 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(x_1, x_4, x_12);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_mk_string_unchecked("grind", 5, 5);
x_47 = lean_mk_string_unchecked("assert", 6, 6);
x_48 = l_Lean_Name_mkStr2(x_46, x_47);
lean_inc(x_48);
x_49 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_48, x_10, x_45);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_48);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_52;
goto block_43;
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_49, 1);
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
x_56 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_54);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_56, 1);
x_59 = lean_ctor_get(x_56, 0);
lean_dec(x_59);
x_60 = lean_mk_string_unchecked("", 0, 0);
x_61 = l_Lean_stringToMessageData(x_60);
lean_dec(x_60);
lean_inc(x_1);
x_62 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_61);
lean_ctor_set_tag(x_56, 7);
lean_ctor_set(x_56, 1, x_62);
lean_ctor_set(x_56, 0, x_61);
lean_ctor_set_tag(x_49, 7);
lean_ctor_set(x_49, 1, x_61);
lean_ctor_set(x_49, 0, x_56);
x_63 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_48, x_49, x_8, x_9, x_10, x_11, x_58);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_64;
goto block_43;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_56, 1);
lean_inc(x_65);
lean_dec(x_56);
x_66 = lean_mk_string_unchecked("", 0, 0);
x_67 = l_Lean_stringToMessageData(x_66);
lean_dec(x_66);
lean_inc(x_1);
x_68 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_67);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set_tag(x_49, 7);
lean_ctor_set(x_49, 1, x_67);
lean_ctor_set(x_49, 0, x_69);
x_70 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_48, x_49, x_8, x_9, x_10, x_11, x_65);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_71;
goto block_43;
}
}
else
{
lean_free_object(x_49);
lean_dec(x_48);
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
lean_dec(x_1);
return x_56;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_49, 1);
lean_inc(x_72);
lean_dec(x_49);
x_73 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
x_76 = lean_mk_string_unchecked("", 0, 0);
x_77 = l_Lean_stringToMessageData(x_76);
lean_dec(x_76);
lean_inc(x_1);
x_78 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_77);
if (lean_is_scalar(x_75)) {
 x_79 = lean_alloc_ctor(7, 2, 0);
} else {
 x_79 = x_75;
 lean_ctor_set_tag(x_79, 7);
}
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
x_81 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_48, x_80, x_8, x_9, x_10, x_11, x_74);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_82;
goto block_43;
}
else
{
lean_dec(x_48);
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
lean_dec(x_1);
return x_73;
}
}
}
block_25:
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
x_24 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(x_2, x_3, x_1, x_23, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_24;
}
block_43:
{
lean_object* x_35; uint8_t x_36; 
lean_inc(x_1);
x_35 = l_Lean_Expr_cleanupAnnotations(x_1);
x_36 = l_Lean_Expr_isApp(x_35);
if (x_36 == 0)
{
lean_dec(x_35);
x_13 = x_26;
x_14 = x_27;
x_15 = x_28;
x_16 = x_29;
x_17 = x_30;
x_18 = x_31;
x_19 = x_32;
x_20 = x_33;
x_21 = x_34;
goto block_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_inc(x_35);
x_37 = l_Lean_Expr_appFnCleanup___redArg(x_35);
x_38 = lean_mk_string_unchecked("Not", 3, 3);
x_39 = l_Lean_Name_mkStr1(x_38);
x_40 = l_Lean_Expr_isConstOf(x_37, x_39);
lean_dec(x_39);
lean_dec(x_37);
if (x_40 == 0)
{
lean_dec(x_35);
x_13 = x_26;
x_14 = x_27;
x_15 = x_28;
x_16 = x_29;
x_17 = x_30;
x_18 = x_31;
x_19 = x_32;
x_20 = x_33;
x_21 = x_34;
goto block_25;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_1);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_dec(x_35);
x_42 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(x_2, x_3, x_41, x_40, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Meta_Grind_isInconsistent___redArg(x_1, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_box(0);
x_15 = lean_unbox(x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_mk_string_unchecked("grind", 5, 5);
x_17 = l_Lean_Core_checkSystem(x_16, x_7, x_8, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(x_1, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_23);
lean_ctor_set(x_19, 0, x_10);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_10);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_free_object(x_10);
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 2);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_27, sizeof(void*)*3);
lean_dec(x_27);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_33 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(x_29, x_30, x_31, x_32, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_9 = x_34;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_dec(x_19);
x_41 = lean_ctor_get(x_27, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_27, 2);
lean_inc(x_43);
lean_dec(x_27);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_44 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(x_41, x_42, x_43, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_9 = x_45;
goto _start;
}
else
{
uint8_t x_47; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
else
{
uint8_t x_51; 
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_17);
if (x_51 == 0)
{
return x_17;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_17, 0);
x_53 = lean_ctor_get(x_17, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_17);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(x_1, x_13);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_14);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_58);
lean_ctor_set(x_55, 0, x_10);
return x_55;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_dec(x_55);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_14);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_60);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_10);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_10, 0);
x_63 = lean_ctor_get(x_10, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_10);
x_64 = lean_box(0);
x_65 = lean_unbox(x_62);
lean_dec(x_62);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_mk_string_unchecked("grind", 5, 5);
x_67 = l_Lean_Core_checkSystem(x_66, x_7, x_8, x_63);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(x_1, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_ctor_set(x_73, 0, x_64);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_64);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_72;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
return x_75;
}
else
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_70, 0);
lean_inc(x_76);
lean_dec(x_70);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_69, 1);
lean_inc(x_77);
lean_dec(x_69);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_76, 2);
lean_inc(x_80);
x_81 = lean_ctor_get_uint8(x_76, sizeof(void*)*3);
lean_dec(x_76);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_82 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(x_78, x_79, x_80, x_81, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_77);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_9 = x_83;
goto _start;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_87 = x_82;
} else {
 lean_dec_ref(x_82);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_69, 1);
lean_inc(x_89);
lean_dec(x_69);
x_90 = lean_ctor_get(x_76, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_76, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_76, 2);
lean_inc(x_92);
lean_dec(x_76);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_93 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(x_90, x_91, x_92, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_89);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_9 = x_94;
goto _start;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = lean_ctor_get(x_93, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_98 = x_93;
} else {
 lean_dec_ref(x_93);
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
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = lean_ctor_get(x_67, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_67, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_102 = x_67;
} else {
 lean_dec_ref(x_67);
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
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_104 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(x_1, x_63);
lean_dec(x_1);
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
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_64);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_64);
if (lean_is_scalar(x_106)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_106;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_105);
return x_109;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
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
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_10, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
lean_inc(x_1);
x_13 = l_Lean_Expr_isTrue(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Meta_Grind_isInconsistent___redArg(x_4, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(x_4, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
return x_20;
}
else
{
uint8_t x_21; 
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
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
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
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_12);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_7);
lean_inc(x_1);
x_12 = l_Lean_FVarId_getType___redArg(x_1, x_7, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_fvar___override(x_1);
x_16 = l_Lean_Meta_Grind_add(x_13, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_16;
}
else
{
uint8_t x_17; 
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
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* initialize_Init_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Inv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_PP(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Ctor(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Beta(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LitValues(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Inv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PP(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Ctor(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Beta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Internalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
