// Lean compiler output
// Module: Lean.Meta.Tactic.SplitIf
// Imports: Lean.Meta.Tactic.Cases Lean.Meta.Tactic.Simp.Main
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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_NumObjs_visit_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f_find_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isDIte(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___Lean_Meta_splitIfTarget_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_toCtorIdx(uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_byCasesDec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getBoundedAppFn(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_NumObjs_visit_spec__1___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_visit_visitApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SplitKind_considerIte(uint8_t);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_visit_visitApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_noConfusion___redArg___lam__0___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0(lean_object*);
extern lean_object* l_Lean_Meta_Simp_neutralConfig;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_simpTarget(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___at___Lean_KeyedDeclsAttribute_mkStateOfTable_spec__1(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_toCtorIdx___boxed(lean_object*);
lean_object* l_Lean_mkPtrSet(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___Lean_Meta_splitIfTarget_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_considerIte___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isIte(lean_object*);
lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_instBEqPtr___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_considerMatch___boxed(lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_instHashablePtr___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_SplitIf___hyg_3743_(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_addConst(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_noConfusion___redArg(uint8_t, uint8_t);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_Meta_SplitKind_considerMatch(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f_find_x3f_unsafe__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_panic___at___Lean_Meta_subst_substEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_num_indices(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelMVars_visitExpr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_toCtorIdx(uint8_t x_1) {
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
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_SplitKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_SplitKind_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SplitKind_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SplitKind_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_SplitKind_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Meta_SplitKind_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SplitKind_considerIte(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_considerIte___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_SplitKind_considerIte(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SplitKind_considerMatch(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitKind_considerMatch___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_SplitKind_considerMatch(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = l_Lean_Expr_getAppNumArgs(x_1);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_sort___override(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_nat_dec_lt(x_4, x_9);
if (x_10 == 0)
{
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_3);
lean_inc(x_5);
x_11 = lean_mk_array(x_5, x_7);
x_12 = lean_nat_sub(x_5, x_8);
lean_dec(x_5);
lean_inc(x_1);
x_13 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_11, x_12);
x_14 = lean_box(0);
x_15 = l_Lean_instInhabitedExpr;
x_16 = lean_array_get(x_15, x_13, x_4);
lean_dec(x_13);
x_17 = l_Lean_Expr_hasLooseBVars(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
x_20 = lean_ctor_get(x_2, 2);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_3 = x_19;
x_4 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_4);
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_14);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; lean_object* x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_array_get_size(x_4);
x_6 = l_Lean_Expr_hash(x_2);
x_7 = lean_unsigned_to_nat(32u);
x_8 = lean_uint64_of_nat(x_7);
x_9 = lean_uint64_shift_right(x_6, x_8);
x_10 = lean_uint64_xor(x_6, x_9);
x_11 = lean_unsigned_to_nat(16u);
x_12 = lean_uint64_of_nat(x_11);
x_13 = lean_uint64_shift_right(x_10, x_12);
x_14 = lean_uint64_xor(x_10, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_sub(x_16, x_18);
x_20 = lean_usize_land(x_15, x_19);
x_21 = lean_array_uget(x_4, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelMVars_visitExpr_spec__0___redArg(x_2, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_2);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_2);
x_24 = lean_box(0);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_47; uint8_t x_48; 
x_47 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_48 = l_Lean_Meta_SplitKind_considerIte(x_47);
if (x_48 == 0)
{
goto block_32;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_mk_string_unchecked("ite", 3, 3);
x_50 = l_Lean_Name_mkStr1(x_49);
x_51 = l_Lean_Expr_isAppOf(x_3, x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_mk_string_unchecked("dite", 4, 4);
x_53 = l_Lean_Name_mkStr1(x_52);
x_54 = l_Lean_Expr_isAppOf(x_3, x_53);
lean_dec(x_53);
if (x_54 == 0)
{
goto block_32;
}
else
{
goto block_46;
}
}
else
{
goto block_46;
}
}
block_32:
{
uint8_t x_4; uint8_t x_5; 
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_5 = l_Lean_Meta_SplitKind_considerMatch(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isMatcherAppCore_x3f(x_1, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = l_Lean_Expr_sort___override(x_10);
x_12 = l_Lean_Expr_getAppNumArgs(x_3);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(x_9);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
x_16 = lean_nat_add(x_14, x_15);
lean_dec(x_15);
lean_inc(x_14);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_13);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_3);
x_21 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(x_3, x_17, x_20, x_14);
lean_dec(x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc(x_12);
x_23 = lean_mk_array(x_12, x_11);
x_24 = lean_nat_sub(x_12, x_13);
lean_dec(x_12);
lean_inc(x_3);
x_25 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_3, x_23, x_24);
x_26 = lean_array_get_size(x_25);
lean_dec(x_25);
x_27 = l_Lean_Meta_Match_MatcherInfo_arity(x_9);
lean_dec(x_9);
x_28 = lean_nat_sub(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
x_29 = l_Lean_Expr_getBoundedAppFn(x_28, x_3);
lean_dec(x_3);
x_30 = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___lam__0(x_2, x_29);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
return x_31;
}
}
}
}
block_39:
{
if (x_35 == 0)
{
lean_dec(x_34);
goto block_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_36 = lean_nat_sub(x_34, x_33);
lean_dec(x_34);
x_37 = l_Lean_Expr_getBoundedAppFn(x_36, x_3);
lean_dec(x_3);
x_38 = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___lam__0(x_2, x_37);
return x_38;
}
}
block_46:
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = l_Lean_Expr_getAppNumArgs(x_3);
x_41 = lean_unsigned_to_nat(5u);
x_42 = lean_nat_dec_le(x_41, x_40);
if (x_42 == 0)
{
x_33 = x_41;
x_34 = x_40;
x_35 = x_42;
goto block_39;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_unsigned_to_nat(3u);
x_44 = l_Lean_Expr_getRevArg_x21(x_3, x_43);
x_45 = l_Lean_Expr_hasLooseBVars(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
x_33 = x_41;
x_34 = x_40;
x_35 = x_42;
goto block_39;
}
else
{
lean_dec(x_40);
goto block_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; lean_object* x_23; size_t x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_instBEqPtr___lam__0___boxed), 2, 0);
x_7 = lean_array_get_size(x_5);
x_8 = lean_ptr_addr(x_1);
x_9 = lean_usize_to_uint64(x_8);
x_10 = lean_unsigned_to_nat(11u);
x_11 = lean_uint64_of_nat(x_10);
x_12 = lean_uint64_mix_hash(x_9, x_11);
x_13 = lean_unsigned_to_nat(32u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_shift_right(x_12, x_14);
x_16 = lean_uint64_xor(x_12, x_15);
x_17 = lean_unsigned_to_nat(16u);
x_18 = lean_uint64_of_nat(x_17);
x_19 = lean_uint64_shift_right(x_16, x_18);
x_20 = lean_uint64_xor(x_16, x_19);
x_21 = lean_uint64_to_usize(x_20);
x_22 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_sub(x_22, x_24);
x_26 = lean_usize_land(x_21, x_25);
x_27 = lean_array_uget(x_5, x_26);
lean_inc(x_27);
lean_inc(x_1);
x_28 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_6, x_1, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_box(0);
if (x_28 == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_2);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_36 = lean_ctor_get(x_2, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_2, 0);
lean_dec(x_37);
x_38 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_29);
lean_ctor_set(x_39, 2, x_27);
x_40 = lean_array_uset(x_5, x_26, x_39);
x_41 = lean_unsigned_to_nat(2u);
x_42 = lean_nat_shiftl(x_38, x_41);
x_43 = lean_unsigned_to_nat(3u);
x_44 = lean_nat_div(x_42, x_43);
lean_dec(x_42);
x_45 = lean_array_get_size(x_40);
x_46 = lean_nat_dec_le(x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_alloc_closure((void*)(l_Lean_instHashablePtr___lam__0___boxed), 1, 0);
x_48 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_47, x_40);
lean_ctor_set(x_2, 1, x_48);
lean_ctor_set(x_2, 0, x_38);
x_30 = x_2;
goto block_34;
}
else
{
lean_ctor_set(x_2, 1, x_40);
lean_ctor_set(x_2, 0, x_38);
x_30 = x_2;
goto block_34;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_2);
x_49 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_29);
lean_ctor_set(x_50, 2, x_27);
x_51 = lean_array_uset(x_5, x_26, x_50);
x_52 = lean_unsigned_to_nat(2u);
x_53 = lean_nat_shiftl(x_49, x_52);
x_54 = lean_unsigned_to_nat(3u);
x_55 = lean_nat_div(x_53, x_54);
lean_dec(x_53);
x_56 = lean_array_get_size(x_51);
x_57 = lean_nat_dec_le(x_55, x_56);
lean_dec(x_56);
lean_dec(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_alloc_closure((void*)(l_Lean_instHashablePtr___lam__0___boxed), 1, 0);
x_59 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_58, x_51);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_49);
lean_ctor_set(x_60, 1, x_59);
x_30 = x_60;
goto block_34;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_49);
lean_ctor_set(x_61, 1, x_51);
x_30 = x_61;
goto block_34;
}
}
}
else
{
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_30 = x_2;
goto block_34;
}
block_34:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_3);
return x_33;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_2);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_3);
return x_64;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; size_t x_26; size_t x_27; lean_object* x_28; size_t x_29; size_t x_30; size_t x_31; lean_object* x_32; uint8_t x_33; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_instBEqPtr___lam__0___boxed), 2, 0);
x_12 = lean_array_get_size(x_10);
x_13 = lean_ptr_addr(x_1);
x_14 = lean_usize_to_uint64(x_13);
x_15 = lean_unsigned_to_nat(11u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_mix_hash(x_14, x_16);
x_18 = lean_unsigned_to_nat(32u);
x_19 = lean_uint64_of_nat(x_18);
x_20 = lean_uint64_shift_right(x_17, x_19);
x_21 = lean_uint64_xor(x_17, x_20);
x_22 = lean_unsigned_to_nat(16u);
x_23 = lean_uint64_of_nat(x_22);
x_24 = lean_uint64_shift_right(x_21, x_23);
x_25 = lean_uint64_xor(x_21, x_24);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_usize_sub(x_27, x_29);
x_31 = lean_usize_land(x_26, x_30);
x_32 = lean_array_uget(x_10, x_31);
lean_inc(x_32);
lean_inc(x_1);
x_33 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_11, x_1, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
if (x_33 == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_3);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_41 = lean_ctor_get(x_3, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_3, 0);
lean_dec(x_42);
x_43 = lean_nat_add(x_9, x_28);
lean_dec(x_9);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_34);
lean_ctor_set(x_44, 2, x_32);
x_45 = lean_array_uset(x_10, x_31, x_44);
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
x_52 = lean_alloc_closure((void*)(l_Lean_instHashablePtr___lam__0___boxed), 1, 0);
x_53 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_52, x_45);
lean_ctor_set(x_3, 1, x_53);
lean_ctor_set(x_3, 0, x_43);
x_35 = x_3;
goto block_39;
}
else
{
lean_ctor_set(x_3, 1, x_45);
lean_ctor_set(x_3, 0, x_43);
x_35 = x_3;
goto block_39;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_3);
x_54 = lean_nat_add(x_9, x_28);
lean_dec(x_9);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_34);
lean_ctor_set(x_55, 2, x_32);
x_56 = lean_array_uset(x_10, x_31, x_55);
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
x_63 = lean_alloc_closure((void*)(l_Lean_instHashablePtr___lam__0___boxed), 1, 0);
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_63, x_56);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_54);
lean_ctor_set(x_65, 1, x_64);
x_35 = x_65;
goto block_39;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_56);
x_35 = x_66;
goto block_39;
}
}
}
else
{
lean_dec(x_32);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_35 = x_3;
goto block_39;
}
block_39:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_8);
return x_38;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_32);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_3);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_8);
return x_69;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_checkVisited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_FindSplitImpl_checkVisited(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_3, 1);
x_27 = lean_nat_dec_lt(x_5, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_7);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_12);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_array_fget(x_1, x_5);
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_array_get_size(x_34);
x_36 = lean_nat_dec_lt(x_5, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_37 = l_Lean_Meta_FindSplitImpl_visit(x_33, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_19 = x_32;
x_20 = x_41;
x_21 = x_40;
goto block_25;
}
else
{
lean_object* x_42; uint8_t x_43; 
lean_dec(x_32);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 1);
x_45 = lean_ctor_get(x_38, 0);
lean_dec(x_45);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_38, 1, x_31);
lean_ctor_set(x_38, 0, x_46);
x_13 = x_38;
x_14 = x_44;
x_15 = x_42;
goto block_18;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_39);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_31);
x_13 = x_49;
x_14 = x_47;
x_15 = x_42;
goto block_18;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_32);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_50 = !lean_is_exclusive(x_37);
if (x_50 == 0)
{
return x_37;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_37, 0);
x_52 = lean_ctor_get(x_37, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_37);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_array_fget(x_34, x_5);
x_55 = lean_ctor_get_uint8(x_54, sizeof(void*)*1 + 2);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = l_Lean_Meta_ParamInfo_isExplicit(x_54);
lean_dec(x_54);
if (x_56 == 0)
{
lean_dec(x_33);
x_19 = x_32;
x_20 = x_7;
x_21 = x_12;
goto block_25;
}
else
{
lean_object* x_57; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_57 = l_Lean_Meta_FindSplitImpl_visit(x_33, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_19 = x_32;
x_20 = x_61;
x_21 = x_60;
goto block_25;
}
else
{
lean_object* x_62; uint8_t x_63; 
lean_dec(x_32);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = !lean_is_exclusive(x_58);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_58, 1);
x_65 = lean_ctor_get(x_58, 0);
lean_dec(x_65);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_59);
lean_ctor_set(x_58, 1, x_31);
lean_ctor_set(x_58, 0, x_66);
x_13 = x_58;
x_14 = x_64;
x_15 = x_62;
goto block_18;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_58, 1);
lean_inc(x_67);
lean_dec(x_58);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_59);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_31);
x_13 = x_69;
x_14 = x_67;
x_15 = x_62;
goto block_18;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_32);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_70 = !lean_is_exclusive(x_57);
if (x_70 == 0)
{
return x_57;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_57, 0);
x_72 = lean_ctor_get(x_57, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_57);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
lean_dec(x_54);
lean_dec(x_33);
x_19 = x_32;
x_20 = x_7;
x_21 = x_12;
goto block_25;
}
}
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
block_25:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_3, 2);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_4 = x_19;
x_5 = x_23;
x_7 = x_20;
x_12 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
lean_dec(x_1);
x_54 = lean_array_set(x_2, x_3, x_53);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_sub(x_3, x_55);
lean_dec(x_3);
x_1 = x_52;
x_2 = x_54;
x_3 = x_56;
goto _start;
}
else
{
uint8_t x_58; 
lean_dec(x_3);
x_58 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_58 == 0)
{
lean_object* x_59; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_59 = l_Lean_Meta_getFunInfo(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_11 = x_60;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
x_18 = x_61;
goto block_51;
}
else
{
uint8_t x_62; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_59);
if (x_62 == 0)
{
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_59);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_mk_empty_array_with_capacity(x_66);
lean_inc(x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_67);
x_11 = x_68;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
x_18 = x_10;
goto block_51;
}
}
block_51:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get_size(x_2);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_26 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(x_2, x_11, x_22, x_25, x_19, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_2);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = l_Lean_Meta_FindSplitImpl_visit(x_1, x_12, x_31, x_14, x_15, x_16, x_17, x_30);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_26, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_27, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_37);
return x_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_dec(x_27);
x_39 = lean_ctor_get(x_29, 0);
lean_inc(x_39);
lean_dec(x_29);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_26, 0, x_40);
return x_26;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_dec(x_26);
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_43 = x_27;
} else {
 lean_dec_ref(x_27);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_29, 0);
lean_inc(x_44);
lean_dec(x_29);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
lean_dec(x_1);
x_54 = lean_array_set(x_2, x_3, x_53);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_sub(x_3, x_55);
x_57 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1_spec__1(x_52, x_54, x_56, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_57;
}
else
{
uint8_t x_58; 
x_58 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_58 == 0)
{
lean_object* x_59; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_59 = l_Lean_Meta_getFunInfo(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_11 = x_60;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
x_18 = x_61;
goto block_51;
}
else
{
uint8_t x_62; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_59);
if (x_62 == 0)
{
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_59);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_mk_empty_array_with_capacity(x_66);
lean_inc(x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_67);
x_11 = x_68;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
x_18 = x_10;
goto block_51;
}
}
block_51:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get_size(x_2);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_26 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(x_2, x_11, x_22, x_25, x_19, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_2);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = l_Lean_Meta_FindSplitImpl_visit(x_1, x_12, x_31, x_14, x_15, x_16, x_17, x_30);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_26, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_27, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_37);
return x_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_dec(x_27);
x_39 = lean_ctor_get(x_29, 0);
lean_inc(x_39);
lean_dec(x_29);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_26, 0, x_40);
return x_26;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_dec(x_26);
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_43 = x_27;
} else {
 lean_dec_ref(x_27);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_29, 0);
lean_inc(x_44);
lean_dec(x_29);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_visit_visitApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_box(0);
x_10 = l_Lean_Expr_sort___override(x_9);
x_11 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_11);
x_12 = lean_mk_array(x_11, x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_11, x_13);
lean_dec(x_11);
x_15 = l_Lean_Expr_withAppAux___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(x_1, x_12, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_43; lean_object* x_86; lean_object* x_87; lean_object* x_88; size_t x_89; uint64_t x_90; lean_object* x_91; uint64_t x_92; uint64_t x_93; lean_object* x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; lean_object* x_98; uint64_t x_99; uint64_t x_100; uint64_t x_101; size_t x_102; size_t x_103; lean_object* x_104; size_t x_105; size_t x_106; size_t x_107; lean_object* x_108; uint8_t x_109; 
x_86 = lean_ctor_get(x_3, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_3, 1);
lean_inc(x_87);
x_88 = lean_array_get_size(x_87);
x_89 = lean_ptr_addr(x_1);
x_90 = lean_usize_to_uint64(x_89);
x_91 = lean_unsigned_to_nat(11u);
x_92 = lean_uint64_of_nat(x_91);
x_93 = lean_uint64_mix_hash(x_90, x_92);
x_94 = lean_unsigned_to_nat(32u);
x_95 = lean_uint64_of_nat(x_94);
x_96 = lean_uint64_shift_right(x_93, x_95);
x_97 = lean_uint64_xor(x_93, x_96);
x_98 = lean_unsigned_to_nat(16u);
x_99 = lean_uint64_of_nat(x_98);
x_100 = lean_uint64_shift_right(x_97, x_99);
x_101 = lean_uint64_xor(x_97, x_100);
x_102 = lean_uint64_to_usize(x_101);
x_103 = lean_usize_of_nat(x_88);
lean_dec(x_88);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_usize_of_nat(x_104);
x_106 = lean_usize_sub(x_103, x_105);
x_107 = lean_usize_land(x_102, x_106);
x_108 = lean_array_uget(x_87, x_107);
x_109 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_NumObjs_visit_spec__0___redArg(x_1, x_108);
if (x_109 == 0)
{
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_3);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_111 = lean_ctor_get(x_3, 1);
lean_dec(x_111);
x_112 = lean_ctor_get(x_3, 0);
lean_dec(x_112);
x_113 = lean_box(0);
x_114 = lean_nat_add(x_86, x_104);
lean_dec(x_86);
lean_inc(x_1);
x_115 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_115, 0, x_1);
lean_ctor_set(x_115, 1, x_113);
lean_ctor_set(x_115, 2, x_108);
x_116 = lean_array_uset(x_87, x_107, x_115);
x_117 = lean_unsigned_to_nat(2u);
x_118 = lean_nat_shiftl(x_114, x_117);
x_119 = lean_unsigned_to_nat(3u);
x_120 = lean_nat_div(x_118, x_119);
lean_dec(x_118);
x_121 = lean_array_get_size(x_116);
x_122 = lean_nat_dec_le(x_120, x_121);
lean_dec(x_121);
lean_dec(x_120);
if (x_122 == 0)
{
lean_object* x_123; 
x_123 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_NumObjs_visit_spec__1___redArg(x_116);
lean_ctor_set(x_3, 1, x_123);
lean_ctor_set(x_3, 0, x_114);
x_43 = x_3;
goto block_85;
}
else
{
lean_ctor_set(x_3, 1, x_116);
lean_ctor_set(x_3, 0, x_114);
x_43 = x_3;
goto block_85;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_dec(x_3);
x_124 = lean_box(0);
x_125 = lean_nat_add(x_86, x_104);
lean_dec(x_86);
lean_inc(x_1);
x_126 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_126, 0, x_1);
lean_ctor_set(x_126, 1, x_124);
lean_ctor_set(x_126, 2, x_108);
x_127 = lean_array_uset(x_87, x_107, x_126);
x_128 = lean_unsigned_to_nat(2u);
x_129 = lean_nat_shiftl(x_125, x_128);
x_130 = lean_unsigned_to_nat(3u);
x_131 = lean_nat_div(x_129, x_130);
lean_dec(x_129);
x_132 = lean_array_get_size(x_127);
x_133 = lean_nat_dec_le(x_131, x_132);
lean_dec(x_132);
lean_dec(x_131);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_NumObjs_visit_spec__1___redArg(x_127);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_125);
lean_ctor_set(x_135, 1, x_134);
x_43 = x_135;
goto block_85;
}
else
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_125);
lean_ctor_set(x_136, 1, x_127);
x_43 = x_136;
goto block_85;
}
}
}
else
{
lean_dec(x_108);
lean_dec(x_87);
lean_dec(x_86);
x_43 = x_3;
goto block_85;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_108);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_137 = lean_box(0);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_3);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_8);
return x_139;
}
block_42:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_17; 
lean_dec(x_9);
x_17 = l_Lean_Meta_FindSplitImpl_visit_visitApp_x3f(x_1, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
case 6:
{
lean_object* x_18; 
lean_dec(x_9);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
lean_dec(x_1);
x_1 = x_18;
x_2 = x_10;
x_3 = x_11;
x_4 = x_12;
x_5 = x_13;
x_6 = x_14;
x_7 = x_15;
x_8 = x_16;
goto _start;
}
case 7:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
lean_dec(x_1);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_22 = l_Lean_Meta_FindSplitImpl_visit(x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_1 = x_21;
x_2 = x_10;
x_3 = x_26;
x_4 = x_12;
x_5 = x_13;
x_6 = x_14;
x_7 = x_15;
x_8 = x_25;
goto _start;
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_22;
}
}
else
{
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_22;
}
}
case 8:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_9);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 3);
lean_inc(x_29);
lean_dec(x_1);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_30 = l_Lean_Meta_FindSplitImpl_visit(x_28, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_1 = x_29;
x_2 = x_10;
x_3 = x_34;
x_4 = x_12;
x_5 = x_13;
x_6 = x_14;
x_7 = x_15;
x_8 = x_33;
goto _start;
}
else
{
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_30;
}
}
else
{
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_30;
}
}
case 10:
{
lean_object* x_36; 
lean_dec(x_9);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
lean_dec(x_1);
x_1 = x_36;
x_2 = x_10;
x_3 = x_11;
x_4 = x_12;
x_5 = x_13;
x_6 = x_14;
x_7 = x_15;
x_8 = x_16;
goto _start;
}
case 11:
{
lean_object* x_38; 
lean_dec(x_9);
x_38 = lean_ctor_get(x_1, 2);
lean_inc(x_38);
lean_dec(x_1);
x_1 = x_38;
x_2 = x_10;
x_3 = x_11;
x_4 = x_12;
x_5 = x_13;
x_6 = x_14;
x_7 = x_15;
x_8 = x_16;
goto _start;
}
default: 
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_9);
lean_ctor_set(x_40, 1, x_11);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_16);
return x_41;
}
}
}
block_85:
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_st_ref_get(x_7, x_8);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_1);
x_49 = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(x_48, x_2, x_1);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
lean_free_object(x_44);
x_50 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_50 == 0)
{
lean_object* x_51; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_51 = l_Lean_Meta_isProof(x_1, x_4, x_5, x_6, x_7, x_47);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_9 = x_49;
x_10 = x_2;
x_11 = x_43;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = x_54;
goto block_42;
}
else
{
uint8_t x_55; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_51);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_51, 0);
lean_dec(x_56);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_49);
lean_ctor_set(x_57, 1, x_43);
lean_ctor_set(x_51, 0, x_57);
return x_51;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_dec(x_51);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_49);
lean_ctor_set(x_59, 1, x_43);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_43);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
x_9 = x_49;
x_10 = x_2;
x_11 = x_43;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = x_47;
goto block_42;
}
}
else
{
lean_object* x_65; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_49);
lean_ctor_set(x_65, 1, x_43);
lean_ctor_set(x_44, 0, x_65);
return x_44;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_44, 0);
x_67 = lean_ctor_get(x_44, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_44);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_1);
x_69 = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(x_68, x_2, x_1);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_70 == 0)
{
lean_object* x_71; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_71 = l_Lean_Meta_isProof(x_1, x_4, x_5, x_6, x_7, x_67);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_9 = x_69;
x_10 = x_2;
x_11 = x_43;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = x_74;
goto block_42;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
 x_76 = lean_box(0);
}
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_69);
lean_ctor_set(x_77, 1, x_43);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_43);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_79 = lean_ctor_get(x_71, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_71, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_81 = x_71;
} else {
 lean_dec_ref(x_71);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
x_9 = x_69;
x_10 = x_2;
x_11 = x_43;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = x_67;
goto block_42;
}
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_69);
lean_ctor_set(x_83, 1, x_43);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_67);
return x_84;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_withAppAux___at___Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_visit_visitApp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_FindSplitImpl_visit_visitApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FindSplitImpl_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_FindSplitImpl_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f_find_x3f_unsafe__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_1);
x_10 = lean_unsigned_to_nat(64u);
x_11 = l_Lean_mkPtrSet(lean_box(0), x_10);
x_12 = l_Lean_Meta_FindSplitImpl_visit(x_3, x_9, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Meta_findSplit_x3f_find_x3f_unsafe__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f_find_x3f(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_findSplit_x3f_find_x3f_unsafe__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
x_15 = lean_mk_string_unchecked("split", 5, 5);
x_16 = lean_mk_string_unchecked("debug", 5, 5);
x_17 = l_Lean_Name_mkStr2(x_15, x_16);
lean_inc(x_17);
x_18 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_17, x_4, x_5, x_6, x_7, x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_17);
lean_dec(x_14);
lean_free_object(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
lean_ctor_set(x_18, 0, x_10);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_mk_string_unchecked("candidate:", 10, 10);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = l_Lean_indentExpr(x_14);
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_28);
lean_ctor_set(x_9, 0, x_27);
x_29 = lean_mk_string_unchecked("", 0, 0);
x_30 = l_Lean_stringToMessageData(x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_9);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_17, x_31, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_10);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_10);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
lean_dec(x_9);
x_38 = lean_ctor_get(x_10, 0);
lean_inc(x_38);
x_39 = lean_mk_string_unchecked("split", 5, 5);
x_40 = lean_mk_string_unchecked("debug", 5, 5);
x_41 = l_Lean_Name_mkStr2(x_39, x_40);
lean_inc(x_41);
x_42 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_41, x_4, x_5, x_6, x_7, x_37);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_10);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_dec(x_42);
x_49 = lean_mk_string_unchecked("candidate:", 10, 10);
x_50 = l_Lean_stringToMessageData(x_49);
lean_dec(x_49);
x_51 = l_Lean_indentExpr(x_38);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_mk_string_unchecked("", 0, 0);
x_54 = l_Lean_stringToMessageData(x_53);
lean_dec(x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_41, x_55, x_4, x_5, x_6, x_7, x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_10);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f_find_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Meta_findSplit_x3f_find_x3f(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f_go(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_14; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_14 = l_Lean_Meta_findSplit_x3f_find_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_27; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_27 = l_Lean_Expr_isIte(x_17);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = l_Lean_Expr_isDIte(x_17);
x_18 = x_28;
goto block_26;
}
else
{
x_18 = x_27;
goto block_26;
}
block_26:
{
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
x_19 = lean_unsigned_to_nat(3u);
x_20 = l_Lean_Expr_getRevArg_x21(x_17, x_19);
x_21 = l_Lean_Meta_findSplit_x3f_go(x_1, x_2, x_20, x_4, x_5, x_6, x_7, x_16);
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
x_9 = x_23;
x_10 = x_17;
goto block_13;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_17);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_9 = x_24;
x_10 = x_25;
goto block_13;
}
}
else
{
lean_dec(x_17);
return x_21;
}
}
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_14;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Meta_findSplit_x3f_go(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1, x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_findSplit_x3f_go(x_2, x_3, x_10, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findSplit_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_findSplit_x3f(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_7 = lean_box(0);
x_8 = lean_unsigned_to_nat(8u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_shiftl(x_8, x_10);
x_12 = lean_unsigned_to_nat(3u);
x_13 = lean_nat_div(x_11, x_12);
lean_dec(x_11);
x_14 = l_Nat_nextPowerOfTwo(x_13);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_unbox(x_7);
x_19 = l_Lean_Meta_findSplit_x3f(x_1, x_18, x_17, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
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
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_19, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = l_Lean_Expr_getRevArg_x21(x_30, x_12);
x_32 = l_Lean_Expr_getRevArg_x21(x_30, x_10);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_20, 0, x_33);
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_20, 0);
lean_inc(x_34);
lean_dec(x_20);
x_35 = l_Lean_Expr_getRevArg_x21(x_34, x_12);
x_36 = l_Lean_Expr_getRevArg_x21(x_34, x_10);
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_19, 0, x_38);
return x_19;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_ctor_get(x_20, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_41 = x_20;
} else {
 lean_dec_ref(x_20);
 x_41 = lean_box(0);
}
x_42 = l_Lean_Expr_getRevArg_x21(x_40, x_12);
x_43 = l_Lean_Expr_getRevArg_x21(x_40, x_10);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
if (lean_is_scalar(x_41)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_41;
}
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_39);
return x_46;
}
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_19);
if (x_47 == 0)
{
return x_19;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_19, 0);
x_49 = lean_ctor_get(x_19, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_19);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_6 = l_Lean_Meta_DiscrTree_empty(lean_box(0));
x_7 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0(lean_box(0));
x_8 = l_Lean_PersistentHashMap_empty___at___Lean_KeyedDeclsAttribute_mkStateOfTable_spec__1(lean_box(0));
x_9 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_inc(x_7);
lean_inc(x_6);
x_11 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_7);
lean_ctor_set(x_11, 3, x_8);
lean_ctor_set(x_11, 4, x_7);
lean_ctor_set(x_11, 5, x_10);
x_12 = lean_mk_string_unchecked("if_pos", 6, 6);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_box(1);
x_15 = lean_box(0);
x_16 = lean_unsigned_to_nat(1000u);
x_17 = lean_unbox(x_14);
x_18 = lean_unbox(x_15);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Meta_SimpTheorems_addConst(x_11, x_13, x_17, x_18, x_16, x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_mk_string_unchecked("if_neg", 6, 6);
x_23 = l_Lean_Name_mkStr1(x_22);
x_24 = lean_unbox(x_14);
x_25 = lean_unbox(x_15);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_26 = l_Lean_Meta_SimpTheorems_addConst(x_20, x_23, x_24, x_25, x_16, x_1, x_2, x_3, x_4, x_21);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_mk_string_unchecked("dif_pos", 7, 7);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = lean_unbox(x_14);
x_32 = lean_unbox(x_15);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_33 = l_Lean_Meta_SimpTheorems_addConst(x_27, x_30, x_31, x_32, x_16, x_1, x_2, x_3, x_4, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_mk_string_unchecked("dif_neg", 7, 7);
x_37 = l_Lean_Name_mkStr1(x_36);
x_38 = lean_unbox(x_14);
x_39 = lean_unbox(x_15);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_40 = l_Lean_Meta_SimpTheorems_addConst(x_34, x_37, x_38, x_39, x_16, x_1, x_2, x_3, x_4, x_35);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Meta_getSimpCongrTheorems(x_3, x_4, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Meta_Simp_neutralConfig;
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_46, sizeof(void*)*2);
x_50 = lean_ctor_get_uint8(x_46, sizeof(void*)*2 + 1);
x_51 = lean_ctor_get_uint8(x_46, sizeof(void*)*2 + 2);
x_52 = lean_ctor_get_uint8(x_46, sizeof(void*)*2 + 3);
x_53 = lean_ctor_get_uint8(x_46, sizeof(void*)*2 + 4);
x_54 = lean_ctor_get_uint8(x_46, sizeof(void*)*2 + 5);
x_55 = lean_ctor_get_uint8(x_46, sizeof(void*)*2 + 6);
x_56 = lean_ctor_get_uint8(x_46, sizeof(void*)*2 + 7);
x_57 = lean_ctor_get_uint8(x_46, sizeof(void*)*2 + 8);
x_58 = lean_ctor_get_uint8(x_46, sizeof(void*)*2 + 9);
x_59 = lean_ctor_get_uint8(x_46, sizeof(void*)*2 + 10);
x_60 = lean_ctor_get_uint8(x_46, sizeof(void*)*2 + 11);
x_61 = lean_ctor_get_uint8(x_46, sizeof(void*)*2 + 13);
x_62 = lean_ctor_get_uint8(x_46, sizeof(void*)*2 + 14);
x_63 = lean_ctor_get_uint8(x_46, sizeof(void*)*2 + 15);
x_64 = lean_ctor_get_uint8(x_46, sizeof(void*)*2 + 16);
x_65 = lean_ctor_get_uint8(x_46, sizeof(void*)*2 + 17);
x_66 = lean_ctor_get_uint8(x_46, sizeof(void*)*2 + 18);
x_67 = lean_ctor_get_uint8(x_46, sizeof(void*)*2 + 19);
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
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 10, x_59);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 11, x_60);
x_69 = lean_unbox(x_15);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 12, x_69);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 13, x_61);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 14, x_62);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 15, x_63);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 16, x_64);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 17, x_65);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 18, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 19, x_67);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_mk_empty_array_with_capacity(x_70);
x_72 = lean_array_push(x_71, x_41);
x_73 = l_Lean_Meta_Simp_mkContext(x_68, x_72, x_44, x_1, x_2, x_3, x_4, x_45);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_73;
}
else
{
uint8_t x_74; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_40);
if (x_74 == 0)
{
return x_40;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_40, 0);
x_76 = lean_ctor_get(x_40, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_40);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_33);
if (x_78 == 0)
{
return x_33;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_33, 0);
x_80 = lean_ctor_get(x_33, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_33);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_26);
if (x_82 == 0)
{
return x_26;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_26, 0);
x_84 = lean_ctor_get(x_26, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_26);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_19);
if (x_86 == 0)
{
return x_19;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_19, 0);
x_88 = lean_ctor_get(x_19, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_19);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_getSimpContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_SplitIf_getSimpContext(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_4, x_10);
if (x_11 == 1)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_4, x_14);
lean_dec(x_4);
x_16 = lean_array_fget(x_3, x_15);
if (lean_obj_tag(x_16) == 0)
{
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_73; lean_object* x_77; lean_object* x_81; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
x_81 = lean_ctor_get(x_18, 0);
lean_inc(x_81);
x_77 = x_81;
goto block_80;
block_72:
{
lean_object* x_21; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_20);
lean_inc(x_1);
x_21 = l_Lean_Meta_isExprDefEq(x_1, x_20, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_mk_string_unchecked("Not", 3, 3);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = l_Lean_Expr_isAppOfArity(x_1, x_26, x_14);
if (x_27 == 0)
{
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_4 = x_15;
x_9 = x_24;
goto _start;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Expr_appArg_x21(x_1);
x_30 = l_Lean_Expr_isAppOfArity(x_29, x_26, x_14);
lean_dec(x_26);
if (x_30 == 0)
{
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_4 = x_15;
x_9 = x_24;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_Expr_appArg_x21(x_29);
lean_dec(x_29);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_32);
x_33 = l_Lean_Meta_isExprDefEq(x_32, x_20, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_19);
lean_dec(x_18);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_4 = x_15;
x_9 = x_36;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_33, 0);
lean_dec(x_39);
x_40 = lean_mk_string_unchecked("not_not_intro", 13, 13);
x_41 = l_Lean_Name_mkStr1(x_40);
x_42 = lean_box(0);
x_43 = l_Lean_Expr_const___override(x_41, x_42);
x_44 = l_Lean_LocalDecl_toExpr(x_18);
x_45 = l_Lean_mkAppB(x_43, x_32, x_44);
if (lean_is_scalar(x_19)) {
 x_46 = lean_alloc_ctor(1, 1, 0);
} else {
 x_46 = x_19;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_33, 0, x_46);
return x_33;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
lean_dec(x_33);
x_48 = lean_mk_string_unchecked("not_not_intro", 13, 13);
x_49 = l_Lean_Name_mkStr1(x_48);
x_50 = lean_box(0);
x_51 = l_Lean_Expr_const___override(x_49, x_50);
x_52 = l_Lean_LocalDecl_toExpr(x_18);
x_53 = l_Lean_mkAppB(x_51, x_32, x_52);
if (lean_is_scalar(x_19)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_19;
}
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_47);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_32);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_33);
if (x_56 == 0)
{
return x_33;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_33, 0);
x_58 = lean_ctor_get(x_33, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_33);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_21);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_21, 0);
lean_dec(x_61);
x_62 = l_Lean_LocalDecl_toExpr(x_18);
if (lean_is_scalar(x_19)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_19;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_21, 0, x_63);
return x_21;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_21, 1);
lean_inc(x_64);
lean_dec(x_21);
x_65 = l_Lean_LocalDecl_toExpr(x_18);
if (lean_is_scalar(x_19)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_19;
}
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_21);
if (x_68 == 0)
{
return x_21;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_21, 0);
x_70 = lean_ctor_get(x_21, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_21);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
block_76:
{
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_18, 3);
lean_inc(x_74);
x_20 = x_74;
goto block_72;
}
else
{
lean_dec(x_19);
lean_dec(x_18);
x_4 = x_15;
goto _start;
}
}
block_80:
{
uint8_t x_78; 
x_78 = lean_nat_dec_le(x_2, x_77);
lean_dec(x_77);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_Lean_LocalDecl_isAuxDecl(x_18);
x_73 = x_79;
goto block_76;
}
else
{
x_73 = x_78;
goto block_76;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_4, x_13);
if (x_14 == 1)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_4, x_17);
lean_dec(x_4);
x_19 = lean_array_fget(x_3, x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_20 = l_Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__1(x_1, x_2, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_4 = x_18;
x_12 = x_22;
goto _start;
}
else
{
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
return x_20;
}
}
else
{
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_array_get_size(x_12);
x_14 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_array_get_size(x_15);
x_17 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_15, x_16, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_array_get_size(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_14 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_12, x_13, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_3, 0);
x_18 = l_Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__1(x_1, x_2, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_18;
}
else
{
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
return x_14;
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 1);
x_13 = l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0___redArg(x_3, x_8, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_122 = lean_mk_string_unchecked("Meta", 4, 4);
x_123 = lean_mk_string_unchecked("Tactic", 6, 6);
x_124 = lean_mk_string_unchecked("splitIf", 7, 7);
x_125 = l_Lean_Name_mkStr3(x_122, x_123, x_124);
lean_inc(x_125);
x_126 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_125, x_9, x_15);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_unbox(x_127);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; 
lean_dec(x_125);
lean_free_object(x_12);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_27 = x_4;
x_28 = x_5;
x_29 = x_6;
x_30 = x_7;
x_31 = x_8;
x_32 = x_9;
x_33 = x_10;
x_34 = x_129;
goto block_121;
}
else
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_126);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_131 = lean_ctor_get(x_126, 1);
x_132 = lean_ctor_get(x_126, 0);
lean_dec(x_132);
x_133 = lean_mk_string_unchecked("discharge\? ", 11, 11);
x_134 = l_Lean_stringToMessageData(x_133);
lean_dec(x_133);
lean_inc(x_14);
x_135 = l_Lean_MessageData_ofExpr(x_14);
lean_ctor_set_tag(x_126, 7);
lean_ctor_set(x_126, 1, x_135);
lean_ctor_set(x_126, 0, x_134);
x_136 = lean_mk_string_unchecked(", ", 2, 2);
x_137 = l_Lean_stringToMessageData(x_136);
lean_dec(x_136);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_137);
lean_ctor_set(x_12, 0, x_126);
x_150 = lean_mk_string_unchecked("Not", 3, 3);
x_151 = l_Lean_Name_mkStr1(x_150);
x_152 = lean_unsigned_to_nat(1u);
x_153 = l_Lean_Expr_isAppOfArity(x_14, x_151, x_152);
if (x_153 == 0)
{
lean_dec(x_151);
goto block_149;
}
else
{
lean_object* x_154; uint8_t x_155; 
x_154 = l_Lean_Expr_appArg_x21(x_14);
x_155 = l_Lean_Expr_isAppOfArity(x_154, x_151, x_152);
lean_dec(x_151);
if (x_155 == 0)
{
lean_dec(x_154);
goto block_149;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = l_Lean_Expr_appArg_x21(x_154);
lean_dec(x_154);
x_157 = l_Lean_MessageData_ofExpr(x_156);
x_138 = x_157;
goto block_145;
}
}
block_145:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_12);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_mk_string_unchecked("", 0, 0);
x_141 = l_Lean_stringToMessageData(x_140);
lean_dec(x_140);
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_125, x_142, x_7, x_8, x_9, x_10, x_131);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
lean_dec(x_143);
x_27 = x_4;
x_28 = x_5;
x_29 = x_6;
x_30 = x_7;
x_31 = x_8;
x_32 = x_9;
x_33 = x_10;
x_34 = x_144;
goto block_121;
}
block_149:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_mk_string_unchecked("<not-available>", 15, 15);
x_147 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_147, 0, x_146);
x_148 = l_Lean_MessageData_ofFormat(x_147);
x_138 = x_148;
goto block_145;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_158 = lean_ctor_get(x_126, 1);
lean_inc(x_158);
lean_dec(x_126);
x_159 = lean_mk_string_unchecked("discharge\? ", 11, 11);
x_160 = l_Lean_stringToMessageData(x_159);
lean_dec(x_159);
lean_inc(x_14);
x_161 = l_Lean_MessageData_ofExpr(x_14);
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_mk_string_unchecked(", ", 2, 2);
x_164 = l_Lean_stringToMessageData(x_163);
lean_dec(x_163);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_164);
lean_ctor_set(x_12, 0, x_162);
x_177 = lean_mk_string_unchecked("Not", 3, 3);
x_178 = l_Lean_Name_mkStr1(x_177);
x_179 = lean_unsigned_to_nat(1u);
x_180 = l_Lean_Expr_isAppOfArity(x_14, x_178, x_179);
if (x_180 == 0)
{
lean_dec(x_178);
goto block_176;
}
else
{
lean_object* x_181; uint8_t x_182; 
x_181 = l_Lean_Expr_appArg_x21(x_14);
x_182 = l_Lean_Expr_isAppOfArity(x_181, x_178, x_179);
lean_dec(x_178);
if (x_182 == 0)
{
lean_dec(x_181);
goto block_176;
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = l_Lean_Expr_appArg_x21(x_181);
lean_dec(x_181);
x_184 = l_Lean_MessageData_ofExpr(x_183);
x_165 = x_184;
goto block_172;
}
}
block_172:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_166 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_166, 0, x_12);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_mk_string_unchecked("", 0, 0);
x_168 = l_Lean_stringToMessageData(x_167);
lean_dec(x_167);
x_169 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_168);
x_170 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_125, x_169, x_7, x_8, x_9, x_10, x_158);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_27 = x_4;
x_28 = x_5;
x_29 = x_6;
x_30 = x_7;
x_31 = x_8;
x_32 = x_9;
x_33 = x_10;
x_34 = x_171;
goto block_121;
}
block_176:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_mk_string_unchecked("<not-available>", 15, 15);
x_174 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_174, 0, x_173);
x_175 = l_Lean_MessageData_ofFormat(x_174);
x_165 = x_175;
goto block_172;
}
}
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 2);
lean_inc(x_24);
x_25 = l_Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(x_14, x_1, x_24, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
lean_dec(x_19);
lean_dec(x_24);
return x_25;
}
block_121:
{
if (x_2 == 0)
{
x_16 = x_27;
x_17 = x_28;
x_18 = x_29;
x_19 = x_30;
x_20 = x_31;
x_21 = x_32;
x_22 = x_33;
x_23 = x_34;
goto block_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc(x_14);
x_35 = l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0___redArg(x_14, x_31, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Expr_hasFVar(x_36);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = l_Lean_Expr_hasMVar(x_36);
if (x_39 == 0)
{
lean_object* x_40; 
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_36);
x_40 = l_Lean_Meta_mkDecide(x_36, x_30, x_31, x_32, x_33, x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; uint8_t x_63; uint64_t x_64; lean_object* x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint8_t x_69; uint64_t x_70; uint64_t x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_box(1);
x_44 = lean_ctor_get(x_30, 0);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_44, 0);
x_46 = lean_ctor_get_uint8(x_44, 1);
x_47 = lean_ctor_get_uint8(x_44, 2);
x_48 = lean_ctor_get_uint8(x_44, 3);
x_49 = lean_ctor_get_uint8(x_44, 4);
x_50 = lean_ctor_get_uint8(x_44, 5);
x_51 = lean_ctor_get_uint8(x_44, 6);
x_52 = lean_ctor_get_uint8(x_44, 7);
x_53 = lean_ctor_get_uint8(x_44, 8);
x_54 = lean_ctor_get_uint8(x_44, 10);
x_55 = lean_ctor_get_uint8(x_44, 11);
x_56 = lean_ctor_get_uint8(x_44, 12);
x_57 = lean_ctor_get_uint8(x_44, 13);
x_58 = lean_ctor_get_uint8(x_44, 14);
x_59 = lean_ctor_get_uint8(x_44, 15);
x_60 = lean_ctor_get_uint8(x_44, 16);
x_61 = lean_ctor_get_uint8(x_44, 17);
lean_dec(x_44);
x_62 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_62, 0, x_45);
lean_ctor_set_uint8(x_62, 1, x_46);
lean_ctor_set_uint8(x_62, 2, x_47);
lean_ctor_set_uint8(x_62, 3, x_48);
lean_ctor_set_uint8(x_62, 4, x_49);
lean_ctor_set_uint8(x_62, 5, x_50);
lean_ctor_set_uint8(x_62, 6, x_51);
lean_ctor_set_uint8(x_62, 7, x_52);
lean_ctor_set_uint8(x_62, 8, x_53);
x_63 = lean_unbox(x_43);
lean_ctor_set_uint8(x_62, 9, x_63);
lean_ctor_set_uint8(x_62, 10, x_54);
lean_ctor_set_uint8(x_62, 11, x_55);
lean_ctor_set_uint8(x_62, 12, x_56);
lean_ctor_set_uint8(x_62, 13, x_57);
lean_ctor_set_uint8(x_62, 14, x_58);
lean_ctor_set_uint8(x_62, 15, x_59);
lean_ctor_set_uint8(x_62, 16, x_60);
lean_ctor_set_uint8(x_62, 17, x_61);
x_64 = lean_ctor_get_uint64(x_30, sizeof(void*)*7);
x_65 = lean_unsigned_to_nat(2u);
x_66 = lean_uint64_of_nat(x_65);
x_67 = lean_uint64_shift_right(x_64, x_66);
x_68 = lean_uint64_shift_left(x_67, x_66);
x_69 = lean_unbox(x_43);
x_70 = l_Lean_Meta_TransparencyMode_toUInt64(x_69);
x_71 = lean_uint64_lor(x_68, x_70);
x_72 = lean_ctor_get_uint8(x_30, sizeof(void*)*7 + 8);
x_73 = lean_ctor_get(x_30, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_30, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_30, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_30, 4);
lean_inc(x_76);
x_77 = lean_ctor_get(x_30, 5);
lean_inc(x_77);
x_78 = lean_ctor_get(x_30, 6);
lean_inc(x_78);
x_79 = lean_ctor_get_uint8(x_30, sizeof(void*)*7 + 9);
x_80 = lean_ctor_get_uint8(x_30, sizeof(void*)*7 + 10);
x_81 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_81, 0, x_62);
lean_ctor_set(x_81, 1, x_73);
lean_ctor_set(x_81, 2, x_74);
lean_ctor_set(x_81, 3, x_75);
lean_ctor_set(x_81, 4, x_76);
lean_ctor_set(x_81, 5, x_77);
lean_ctor_set(x_81, 6, x_78);
lean_ctor_set_uint64(x_81, sizeof(void*)*7, x_71);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 8, x_72);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 9, x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 10, x_80);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_41);
x_82 = lean_whnf(x_41, x_81, x_31, x_32, x_33, x_42);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_mk_string_unchecked("Bool", 4, 4);
x_86 = lean_mk_string_unchecked("true", 4, 4);
x_87 = l_Lean_Name_mkStr2(x_85, x_86);
x_88 = l_Lean_Expr_isConstOf(x_83, x_87);
lean_dec(x_83);
if (x_88 == 0)
{
lean_dec(x_87);
lean_dec(x_41);
lean_dec(x_36);
x_16 = x_27;
x_17 = x_28;
x_18 = x_29;
x_19 = x_30;
x_20 = x_31;
x_21 = x_32;
x_22 = x_33;
x_23 = x_84;
goto block_26;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_14);
x_89 = lean_box(0);
x_90 = l_Lean_Expr_const___override(x_87, x_89);
x_91 = l_Lean_Meta_mkEqRefl(x_90, x_30, x_31, x_32, x_33, x_84);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_mk_string_unchecked("of_decide_eq_true", 17, 17);
x_95 = l_Lean_Name_mkStr1(x_94);
x_96 = l_Lean_Expr_const___override(x_95, x_89);
x_97 = l_Lean_Expr_appArg_x21(x_41);
lean_dec(x_41);
x_98 = l_Lean_mkApp3(x_96, x_36, x_97, x_93);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_91, 0, x_99);
return x_91;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_100 = lean_ctor_get(x_91, 0);
x_101 = lean_ctor_get(x_91, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_91);
x_102 = lean_mk_string_unchecked("of_decide_eq_true", 17, 17);
x_103 = l_Lean_Name_mkStr1(x_102);
x_104 = l_Lean_Expr_const___override(x_103, x_89);
x_105 = l_Lean_Expr_appArg_x21(x_41);
lean_dec(x_41);
x_106 = l_Lean_mkApp3(x_104, x_36, x_105, x_100);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_101);
return x_108;
}
}
else
{
uint8_t x_109; 
lean_dec(x_41);
lean_dec(x_36);
x_109 = !lean_is_exclusive(x_91);
if (x_109 == 0)
{
return x_91;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_91, 0);
x_111 = lean_ctor_get(x_91, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_91);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_41);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_14);
x_113 = !lean_is_exclusive(x_82);
if (x_113 == 0)
{
return x_82;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_82, 0);
x_115 = lean_ctor_get(x_82, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_82);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_14);
x_117 = !lean_is_exclusive(x_40);
if (x_117 == 0)
{
return x_40;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_40, 0);
x_119 = lean_ctor_get(x_40, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_40);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_dec(x_36);
x_16 = x_27;
x_17 = x_28;
x_18 = x_29;
x_19 = x_30;
x_20 = x_31;
x_21 = x_32;
x_22 = x_33;
x_23 = x_37;
goto block_26;
}
}
else
{
lean_dec(x_36);
x_16 = x_27;
x_17 = x_28;
x_18 = x_29;
x_19 = x_30;
x_20 = x_31;
x_21 = x_32;
x_22 = x_33;
x_23 = x_37;
goto block_26;
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_185 = lean_ctor_get(x_12, 0);
x_186 = lean_ctor_get(x_12, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_12);
x_286 = lean_mk_string_unchecked("Meta", 4, 4);
x_287 = lean_mk_string_unchecked("Tactic", 6, 6);
x_288 = lean_mk_string_unchecked("splitIf", 7, 7);
x_289 = l_Lean_Name_mkStr3(x_286, x_287, x_288);
lean_inc(x_289);
x_290 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_289, x_9, x_186);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_unbox(x_291);
lean_dec(x_291);
if (x_292 == 0)
{
lean_object* x_293; 
lean_dec(x_289);
x_293 = lean_ctor_get(x_290, 1);
lean_inc(x_293);
lean_dec(x_290);
x_198 = x_4;
x_199 = x_5;
x_200 = x_6;
x_201 = x_7;
x_202 = x_8;
x_203 = x_9;
x_204 = x_10;
x_205 = x_293;
goto block_285;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_294 = lean_ctor_get(x_290, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_295 = x_290;
} else {
 lean_dec_ref(x_290);
 x_295 = lean_box(0);
}
x_296 = lean_mk_string_unchecked("discharge\? ", 11, 11);
x_297 = l_Lean_stringToMessageData(x_296);
lean_dec(x_296);
lean_inc(x_185);
x_298 = l_Lean_MessageData_ofExpr(x_185);
if (lean_is_scalar(x_295)) {
 x_299 = lean_alloc_ctor(7, 2, 0);
} else {
 x_299 = x_295;
 lean_ctor_set_tag(x_299, 7);
}
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
x_300 = lean_mk_string_unchecked(", ", 2, 2);
x_301 = l_Lean_stringToMessageData(x_300);
lean_dec(x_300);
x_302 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_302, 0, x_299);
lean_ctor_set(x_302, 1, x_301);
x_315 = lean_mk_string_unchecked("Not", 3, 3);
x_316 = l_Lean_Name_mkStr1(x_315);
x_317 = lean_unsigned_to_nat(1u);
x_318 = l_Lean_Expr_isAppOfArity(x_185, x_316, x_317);
if (x_318 == 0)
{
lean_dec(x_316);
goto block_314;
}
else
{
lean_object* x_319; uint8_t x_320; 
x_319 = l_Lean_Expr_appArg_x21(x_185);
x_320 = l_Lean_Expr_isAppOfArity(x_319, x_316, x_317);
lean_dec(x_316);
if (x_320 == 0)
{
lean_dec(x_319);
goto block_314;
}
else
{
lean_object* x_321; lean_object* x_322; 
x_321 = l_Lean_Expr_appArg_x21(x_319);
lean_dec(x_319);
x_322 = l_Lean_MessageData_ofExpr(x_321);
x_303 = x_322;
goto block_310;
}
}
block_310:
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_304 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
x_305 = lean_mk_string_unchecked("", 0, 0);
x_306 = l_Lean_stringToMessageData(x_305);
lean_dec(x_305);
x_307 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_307, 0, x_304);
lean_ctor_set(x_307, 1, x_306);
x_308 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_289, x_307, x_7, x_8, x_9, x_10, x_294);
x_309 = lean_ctor_get(x_308, 1);
lean_inc(x_309);
lean_dec(x_308);
x_198 = x_4;
x_199 = x_5;
x_200 = x_6;
x_201 = x_7;
x_202 = x_8;
x_203 = x_9;
x_204 = x_10;
x_205 = x_309;
goto block_285;
}
block_314:
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_mk_string_unchecked("<not-available>", 15, 15);
x_312 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_312, 0, x_311);
x_313 = l_Lean_MessageData_ofFormat(x_312);
x_303 = x_313;
goto block_310;
}
}
block_197:
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_190, 2);
lean_inc(x_195);
x_196 = l_Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(x_185, x_1, x_195, x_187, x_188, x_189, x_190, x_191, x_192, x_193, x_194);
lean_dec(x_190);
lean_dec(x_195);
return x_196;
}
block_285:
{
if (x_2 == 0)
{
x_187 = x_198;
x_188 = x_199;
x_189 = x_200;
x_190 = x_201;
x_191 = x_202;
x_192 = x_203;
x_193 = x_204;
x_194 = x_205;
goto block_197;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
lean_inc(x_185);
x_206 = l_Lean_instantiateMVars___at___Lean_Meta_Simp_synthesizeArgs_spec__0___redArg(x_185, x_202, x_205);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = l_Lean_Expr_hasFVar(x_207);
if (x_209 == 0)
{
uint8_t x_210; 
x_210 = l_Lean_Expr_hasMVar(x_207);
if (x_210 == 0)
{
lean_object* x_211; 
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_207);
x_211 = l_Lean_Meta_mkDecide(x_207, x_201, x_202, x_203, x_204, x_208);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; uint8_t x_217; uint8_t x_218; uint8_t x_219; uint8_t x_220; uint8_t x_221; uint8_t x_222; uint8_t x_223; uint8_t x_224; uint8_t x_225; uint8_t x_226; uint8_t x_227; uint8_t x_228; uint8_t x_229; uint8_t x_230; uint8_t x_231; uint8_t x_232; lean_object* x_233; uint8_t x_234; uint64_t x_235; lean_object* x_236; uint64_t x_237; uint64_t x_238; uint64_t x_239; uint8_t x_240; uint64_t x_241; uint64_t x_242; uint8_t x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = lean_box(1);
x_215 = lean_ctor_get(x_201, 0);
lean_inc(x_215);
x_216 = lean_ctor_get_uint8(x_215, 0);
x_217 = lean_ctor_get_uint8(x_215, 1);
x_218 = lean_ctor_get_uint8(x_215, 2);
x_219 = lean_ctor_get_uint8(x_215, 3);
x_220 = lean_ctor_get_uint8(x_215, 4);
x_221 = lean_ctor_get_uint8(x_215, 5);
x_222 = lean_ctor_get_uint8(x_215, 6);
x_223 = lean_ctor_get_uint8(x_215, 7);
x_224 = lean_ctor_get_uint8(x_215, 8);
x_225 = lean_ctor_get_uint8(x_215, 10);
x_226 = lean_ctor_get_uint8(x_215, 11);
x_227 = lean_ctor_get_uint8(x_215, 12);
x_228 = lean_ctor_get_uint8(x_215, 13);
x_229 = lean_ctor_get_uint8(x_215, 14);
x_230 = lean_ctor_get_uint8(x_215, 15);
x_231 = lean_ctor_get_uint8(x_215, 16);
x_232 = lean_ctor_get_uint8(x_215, 17);
lean_dec(x_215);
x_233 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_233, 0, x_216);
lean_ctor_set_uint8(x_233, 1, x_217);
lean_ctor_set_uint8(x_233, 2, x_218);
lean_ctor_set_uint8(x_233, 3, x_219);
lean_ctor_set_uint8(x_233, 4, x_220);
lean_ctor_set_uint8(x_233, 5, x_221);
lean_ctor_set_uint8(x_233, 6, x_222);
lean_ctor_set_uint8(x_233, 7, x_223);
lean_ctor_set_uint8(x_233, 8, x_224);
x_234 = lean_unbox(x_214);
lean_ctor_set_uint8(x_233, 9, x_234);
lean_ctor_set_uint8(x_233, 10, x_225);
lean_ctor_set_uint8(x_233, 11, x_226);
lean_ctor_set_uint8(x_233, 12, x_227);
lean_ctor_set_uint8(x_233, 13, x_228);
lean_ctor_set_uint8(x_233, 14, x_229);
lean_ctor_set_uint8(x_233, 15, x_230);
lean_ctor_set_uint8(x_233, 16, x_231);
lean_ctor_set_uint8(x_233, 17, x_232);
x_235 = lean_ctor_get_uint64(x_201, sizeof(void*)*7);
x_236 = lean_unsigned_to_nat(2u);
x_237 = lean_uint64_of_nat(x_236);
x_238 = lean_uint64_shift_right(x_235, x_237);
x_239 = lean_uint64_shift_left(x_238, x_237);
x_240 = lean_unbox(x_214);
x_241 = l_Lean_Meta_TransparencyMode_toUInt64(x_240);
x_242 = lean_uint64_lor(x_239, x_241);
x_243 = lean_ctor_get_uint8(x_201, sizeof(void*)*7 + 8);
x_244 = lean_ctor_get(x_201, 1);
lean_inc(x_244);
x_245 = lean_ctor_get(x_201, 2);
lean_inc(x_245);
x_246 = lean_ctor_get(x_201, 3);
lean_inc(x_246);
x_247 = lean_ctor_get(x_201, 4);
lean_inc(x_247);
x_248 = lean_ctor_get(x_201, 5);
lean_inc(x_248);
x_249 = lean_ctor_get(x_201, 6);
lean_inc(x_249);
x_250 = lean_ctor_get_uint8(x_201, sizeof(void*)*7 + 9);
x_251 = lean_ctor_get_uint8(x_201, sizeof(void*)*7 + 10);
x_252 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_252, 0, x_233);
lean_ctor_set(x_252, 1, x_244);
lean_ctor_set(x_252, 2, x_245);
lean_ctor_set(x_252, 3, x_246);
lean_ctor_set(x_252, 4, x_247);
lean_ctor_set(x_252, 5, x_248);
lean_ctor_set(x_252, 6, x_249);
lean_ctor_set_uint64(x_252, sizeof(void*)*7, x_242);
lean_ctor_set_uint8(x_252, sizeof(void*)*7 + 8, x_243);
lean_ctor_set_uint8(x_252, sizeof(void*)*7 + 9, x_250);
lean_ctor_set_uint8(x_252, sizeof(void*)*7 + 10, x_251);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_212);
x_253 = lean_whnf(x_212, x_252, x_202, x_203, x_204, x_213);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = lean_mk_string_unchecked("Bool", 4, 4);
x_257 = lean_mk_string_unchecked("true", 4, 4);
x_258 = l_Lean_Name_mkStr2(x_256, x_257);
x_259 = l_Lean_Expr_isConstOf(x_254, x_258);
lean_dec(x_254);
if (x_259 == 0)
{
lean_dec(x_258);
lean_dec(x_212);
lean_dec(x_207);
x_187 = x_198;
x_188 = x_199;
x_189 = x_200;
x_190 = x_201;
x_191 = x_202;
x_192 = x_203;
x_193 = x_204;
x_194 = x_255;
goto block_197;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_185);
x_260 = lean_box(0);
x_261 = l_Lean_Expr_const___override(x_258, x_260);
x_262 = l_Lean_Meta_mkEqRefl(x_261, x_201, x_202, x_203, x_204, x_255);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_265 = x_262;
} else {
 lean_dec_ref(x_262);
 x_265 = lean_box(0);
}
x_266 = lean_mk_string_unchecked("of_decide_eq_true", 17, 17);
x_267 = l_Lean_Name_mkStr1(x_266);
x_268 = l_Lean_Expr_const___override(x_267, x_260);
x_269 = l_Lean_Expr_appArg_x21(x_212);
lean_dec(x_212);
x_270 = l_Lean_mkApp3(x_268, x_207, x_269, x_263);
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_270);
if (lean_is_scalar(x_265)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_265;
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_264);
return x_272;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_212);
lean_dec(x_207);
x_273 = lean_ctor_get(x_262, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_262, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_275 = x_262;
} else {
 lean_dec_ref(x_262);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_212);
lean_dec(x_207);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_185);
x_277 = lean_ctor_get(x_253, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_253, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_279 = x_253;
} else {
 lean_dec_ref(x_253);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(1, 2, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_277);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_207);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_185);
x_281 = lean_ctor_get(x_211, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_211, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_283 = x_211;
} else {
 lean_dec_ref(x_211);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
else
{
lean_dec(x_207);
x_187 = x_198;
x_188 = x_199;
x_189 = x_200;
x_190 = x_201;
x_191 = x_202;
x_192 = x_203;
x_193 = x_204;
x_194 = x_208;
goto block_197;
}
}
else
{
lean_dec(x_207);
x_187 = x_198;
x_188 = x_199;
x_189 = x_200;
x_190 = x_201;
x_191 = x_202;
x_192 = x_203;
x_193 = x_204;
x_194 = x_208;
goto block_197;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_LocalContext_findDeclRevM_x3f___at_____private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_local_ctx_num_indices(x_4);
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed), 11, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(x_1, x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_Meta_SplitIf_mkDischarge_x3f(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1, x_5, x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_15);
x_17 = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(x_15, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_mk_string_unchecked("Meta", 4, 4);
x_21 = lean_mk_string_unchecked("Tactic", 6, 6);
x_22 = lean_mk_string_unchecked("splitIf", 7, 7);
x_23 = l_Lean_Name_mkStr3(x_20, x_21, x_22);
lean_inc(x_23);
x_24 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_23, x_4, x_5, x_6, x_7, x_19);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_23);
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_9 = x_27;
goto block_12;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_24, 1);
x_30 = lean_ctor_get(x_24, 0);
lean_dec(x_30);
x_31 = lean_mk_string_unchecked("could not find if to split:", 27, 27);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = l_Lean_indentExpr(x_15);
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_33);
lean_ctor_set(x_24, 0, x_32);
x_34 = lean_mk_string_unchecked("", 0, 0);
x_35 = l_Lean_stringToMessageData(x_34);
lean_dec(x_34);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_35);
lean_ctor_set(x_13, 0, x_24);
x_36 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_23, x_13, x_4, x_5, x_6, x_7, x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_9 = x_37;
goto block_12;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_dec(x_24);
x_39 = lean_mk_string_unchecked("could not find if to split:", 27, 27);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = l_Lean_indentExpr(x_15);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_mk_string_unchecked("", 0, 0);
x_44 = l_Lean_stringToMessageData(x_43);
lean_dec(x_43);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_44);
lean_ctor_set(x_13, 0, x_42);
x_45 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_23, x_13, x_4, x_5, x_6, x_7, x_38);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_9 = x_46;
goto block_12;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_free_object(x_13);
lean_dec(x_15);
x_47 = lean_ctor_get(x_18, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_48 = x_18;
} else {
 lean_dec_ref(x_18);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_17, 1);
lean_inc(x_49);
lean_dec(x_17);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_52 = x_47;
} else {
 lean_dec_ref(x_47);
 x_52 = lean_box(0);
}
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_mk_string_unchecked("h", 1, 1);
x_109 = l_Lean_Name_mkStr1(x_108);
x_110 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_109, x_6, x_7, x_49);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_72 = x_111;
x_73 = x_4;
x_74 = x_5;
x_75 = x_6;
x_76 = x_7;
x_77 = x_112;
goto block_107;
}
else
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_3, 0);
lean_inc(x_113);
lean_dec(x_3);
x_72 = x_113;
x_73 = x_4;
x_74 = x_5;
x_75 = x_6;
x_76 = x_7;
x_77 = x_49;
goto block_107;
}
block_71:
{
lean_object* x_59; 
x_59 = l_Lean_MVarId_byCasesDec(x_2, x_50, x_51, x_53, x_54, x_55, x_56, x_57, x_58);
lean_dec(x_54);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
if (lean_is_scalar(x_48)) {
 x_62 = lean_alloc_ctor(1, 1, 0);
} else {
 x_62 = x_48;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_59, 0, x_62);
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_59);
if (lean_is_scalar(x_48)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_48;
}
lean_ctor_set(x_65, 0, x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_48);
x_67 = !lean_is_exclusive(x_59);
if (x_67 == 0)
{
return x_59;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_59, 0);
x_69 = lean_ctor_get(x_59, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_59);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
block_107:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_78 = lean_mk_string_unchecked("Meta", 4, 4);
x_79 = lean_mk_string_unchecked("Tactic", 6, 6);
x_80 = lean_mk_string_unchecked("splitIf", 7, 7);
x_81 = l_Lean_Name_mkStr3(x_78, x_79, x_80);
lean_inc(x_81);
x_82 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_81, x_73, x_74, x_75, x_76, x_77);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_81);
lean_dec(x_52);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_53 = x_72;
x_54 = x_73;
x_55 = x_74;
x_56 = x_75;
x_57 = x_76;
x_58 = x_85;
goto block_71;
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_82);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_87 = lean_ctor_get(x_82, 1);
x_88 = lean_ctor_get(x_82, 0);
lean_dec(x_88);
x_89 = lean_mk_string_unchecked("splitting on ", 13, 13);
x_90 = l_Lean_stringToMessageData(x_89);
lean_dec(x_89);
lean_inc(x_51);
x_91 = l_Lean_MessageData_ofExpr(x_51);
lean_ctor_set_tag(x_82, 7);
lean_ctor_set(x_82, 1, x_91);
lean_ctor_set(x_82, 0, x_90);
x_92 = lean_mk_string_unchecked("", 0, 0);
x_93 = l_Lean_stringToMessageData(x_92);
lean_dec(x_92);
if (lean_is_scalar(x_52)) {
 x_94 = lean_alloc_ctor(7, 2, 0);
} else {
 x_94 = x_52;
 lean_ctor_set_tag(x_94, 7);
}
lean_ctor_set(x_94, 0, x_82);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_81, x_94, x_73, x_74, x_75, x_76, x_87);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_53 = x_72;
x_54 = x_73;
x_55 = x_74;
x_56 = x_75;
x_57 = x_76;
x_58 = x_96;
goto block_71;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_97 = lean_ctor_get(x_82, 1);
lean_inc(x_97);
lean_dec(x_82);
x_98 = lean_mk_string_unchecked("splitting on ", 13, 13);
x_99 = l_Lean_stringToMessageData(x_98);
lean_dec(x_98);
lean_inc(x_51);
x_100 = l_Lean_MessageData_ofExpr(x_51);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_mk_string_unchecked("", 0, 0);
x_103 = l_Lean_stringToMessageData(x_102);
lean_dec(x_102);
if (lean_is_scalar(x_52)) {
 x_104 = lean_alloc_ctor(7, 2, 0);
} else {
 x_104 = x_52;
 lean_ctor_set_tag(x_104, 7);
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_81, x_104, x_73, x_74, x_75, x_76, x_97);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_53 = x_72;
x_54 = x_73;
x_55 = x_74;
x_56 = x_75;
x_57 = x_76;
x_58 = x_106;
goto block_71;
}
}
}
}
}
else
{
uint8_t x_114; 
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_114 = !lean_is_exclusive(x_17);
if (x_114 == 0)
{
return x_17;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_17, 0);
x_116 = lean_ctor_get(x_17, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_17);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_13, 0);
x_119 = lean_ctor_get(x_13, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_118);
x_120 = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(x_118, x_4, x_5, x_6, x_7, x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
lean_dec(x_3);
lean_dec(x_2);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_mk_string_unchecked("Meta", 4, 4);
x_124 = lean_mk_string_unchecked("Tactic", 6, 6);
x_125 = lean_mk_string_unchecked("splitIf", 7, 7);
x_126 = l_Lean_Name_mkStr3(x_123, x_124, x_125);
lean_inc(x_126);
x_127 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_126, x_4, x_5, x_6, x_7, x_122);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_unbox(x_128);
lean_dec(x_128);
if (x_129 == 0)
{
lean_object* x_130; 
lean_dec(x_126);
lean_dec(x_118);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_9 = x_130;
goto block_12;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_131 = lean_ctor_get(x_127, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_132 = x_127;
} else {
 lean_dec_ref(x_127);
 x_132 = lean_box(0);
}
x_133 = lean_mk_string_unchecked("could not find if to split:", 27, 27);
x_134 = l_Lean_stringToMessageData(x_133);
lean_dec(x_133);
x_135 = l_Lean_indentExpr(x_118);
if (lean_is_scalar(x_132)) {
 x_136 = lean_alloc_ctor(7, 2, 0);
} else {
 x_136 = x_132;
 lean_ctor_set_tag(x_136, 7);
}
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_mk_string_unchecked("", 0, 0);
x_138 = l_Lean_stringToMessageData(x_137);
lean_dec(x_137);
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_138);
x_140 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_126, x_139, x_4, x_5, x_6, x_7, x_131);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_9 = x_141;
goto block_12;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_118);
x_142 = lean_ctor_get(x_121, 0);
lean_inc(x_142);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_143 = x_121;
} else {
 lean_dec_ref(x_121);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_120, 1);
lean_inc(x_144);
lean_dec(x_120);
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_147 = x_142;
} else {
 lean_dec_ref(x_142);
 x_147 = lean_box(0);
}
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_191 = lean_mk_string_unchecked("h", 1, 1);
x_192 = l_Lean_Name_mkStr1(x_191);
x_193 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_192, x_6, x_7, x_144);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_165 = x_194;
x_166 = x_4;
x_167 = x_5;
x_168 = x_6;
x_169 = x_7;
x_170 = x_195;
goto block_190;
}
else
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_3, 0);
lean_inc(x_196);
lean_dec(x_3);
x_165 = x_196;
x_166 = x_4;
x_167 = x_5;
x_168 = x_6;
x_169 = x_7;
x_170 = x_144;
goto block_190;
}
block_164:
{
lean_object* x_154; 
x_154 = l_Lean_MVarId_byCasesDec(x_2, x_145, x_146, x_148, x_149, x_150, x_151, x_152, x_153);
lean_dec(x_149);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_157 = x_154;
} else {
 lean_dec_ref(x_154);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_158 = lean_alloc_ctor(1, 1, 0);
} else {
 x_158 = x_143;
}
lean_ctor_set(x_158, 0, x_155);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_156);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_143);
x_160 = lean_ctor_get(x_154, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_154, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_162 = x_154;
} else {
 lean_dec_ref(x_154);
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
block_190:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_171 = lean_mk_string_unchecked("Meta", 4, 4);
x_172 = lean_mk_string_unchecked("Tactic", 6, 6);
x_173 = lean_mk_string_unchecked("splitIf", 7, 7);
x_174 = l_Lean_Name_mkStr3(x_171, x_172, x_173);
lean_inc(x_174);
x_175 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_174, x_166, x_167, x_168, x_169, x_170);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_unbox(x_176);
lean_dec(x_176);
if (x_177 == 0)
{
lean_object* x_178; 
lean_dec(x_174);
lean_dec(x_147);
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
lean_dec(x_175);
x_148 = x_165;
x_149 = x_166;
x_150 = x_167;
x_151 = x_168;
x_152 = x_169;
x_153 = x_178;
goto block_164;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_179 = lean_ctor_get(x_175, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_180 = x_175;
} else {
 lean_dec_ref(x_175);
 x_180 = lean_box(0);
}
x_181 = lean_mk_string_unchecked("splitting on ", 13, 13);
x_182 = l_Lean_stringToMessageData(x_181);
lean_dec(x_181);
lean_inc(x_146);
x_183 = l_Lean_MessageData_ofExpr(x_146);
if (lean_is_scalar(x_180)) {
 x_184 = lean_alloc_ctor(7, 2, 0);
} else {
 x_184 = x_180;
 lean_ctor_set_tag(x_184, 7);
}
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_mk_string_unchecked("", 0, 0);
x_186 = l_Lean_stringToMessageData(x_185);
lean_dec(x_185);
if (lean_is_scalar(x_147)) {
 x_187 = lean_alloc_ctor(7, 2, 0);
} else {
 x_187 = x_147;
 lean_ctor_set_tag(x_187, 7);
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_186);
x_188 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_174, x_187, x_166, x_167, x_168, x_169, x_179);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
x_148 = x_165;
x_149 = x_166;
x_150 = x_167;
x_151 = x_168;
x_152 = x_169;
x_153 = x_189;
goto block_164;
}
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_118);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_197 = lean_ctor_get(x_120, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_120, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_199 = x_120;
} else {
 lean_dec_ref(x_120);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
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
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0), 8, 3);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_3);
x_10 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SplitIf_splitIfAt_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SplitIf_splitIfAt_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Meta_SplitIf_getSimpContext(x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed), 6, 1);
lean_closure_set(x_12, 0, x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_13 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_12, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Array_empty(lean_box(0));
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_18 = lean_box(0);
x_19 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_19);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_unsigned_to_nat(0u);
lean_inc(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_19);
x_24 = lean_unsigned_to_nat(2u);
x_25 = lean_unsigned_to_nat(5u);
x_26 = lean_usize_of_nat(x_25);
x_27 = lean_usize_to_nat(x_26);
x_28 = lean_nat_pow(x_24, x_27);
lean_dec(x_27);
x_29 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_30 = lean_usize_to_nat(x_29);
x_31 = lean_mk_empty_array_with_capacity(x_30);
lean_dec(x_30);
lean_inc(x_31);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_21);
lean_ctor_set(x_33, 3, x_21);
lean_ctor_set_usize(x_33, 4, x_26);
lean_inc(x_20);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_20);
lean_ctor_set(x_34, 1, x_20);
lean_ctor_set(x_34, 2, x_23);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_unbox(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_37 = l_Lean_Meta_simpTarget(x_1, x_9, x_16, x_17, x_36, x_35, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_mk_string_unchecked("Lean.Meta.Tactic.SplitIf", 24, 24);
x_42 = lean_mk_string_unchecked("Lean.Meta.simpIfTarget", 22, 22);
x_43 = lean_unsigned_to_nat(204u);
x_44 = lean_unsigned_to_nat(4u);
x_45 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_46 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_41, x_42, x_43, x_44, x_45);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_41);
x_47 = l_panic___at___Lean_Meta_subst_substEq_spec__0(x_46, x_3, x_4, x_5, x_6, x_40);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_37);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_37, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_39, 0);
lean_inc(x_50);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_50);
return x_37;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
lean_dec(x_37);
x_52 = lean_ctor_get(x_39, 0);
lean_inc(x_52);
lean_dec(x_39);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_37);
if (x_54 == 0)
{
return x_37;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_37, 0);
x_56 = lean_ctor_get(x_37, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_37);
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
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_13);
if (x_58 == 0)
{
return x_13;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_13, 0);
x_60 = lean_ctor_get(x_13, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_13);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_8);
if (x_62 == 0)
{
return x_8;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_8, 0);
x_64 = lean_ctor_get(x_8, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_8);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_simpIfTarget(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_simpIfLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Meta_SplitIf_getSimpContext(x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed), 6, 1);
lean_closure_set(x_12, 0, x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_13 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_12, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Array_empty(lean_box(0));
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_18 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_18);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_unsigned_to_nat(0u);
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_18);
x_23 = lean_unsigned_to_nat(2u);
x_24 = lean_unsigned_to_nat(5u);
x_25 = lean_usize_of_nat(x_24);
x_26 = lean_usize_to_nat(x_25);
x_27 = lean_nat_pow(x_23, x_26);
lean_dec(x_26);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_29 = lean_usize_to_nat(x_28);
x_30 = lean_mk_empty_array_with_capacity(x_29);
lean_dec(x_29);
lean_inc(x_30);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_20);
lean_ctor_set(x_32, 3, x_20);
lean_ctor_set_usize(x_32, 4, x_25);
lean_inc(x_19);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_19);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_unbox(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_36 = l_Lean_Meta_simpLocalDecl(x_1, x_2, x_9, x_16, x_17, x_35, x_34, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_mk_string_unchecked("Lean.Meta.Tactic.SplitIf", 24, 24);
x_41 = lean_mk_string_unchecked("Lean.Meta.simpIfLocalDecl", 25, 25);
x_42 = lean_unsigned_to_nat(211u);
x_43 = lean_unsigned_to_nat(4u);
x_44 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_45 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_40, x_41, x_42, x_43, x_44);
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_40);
x_46 = l_panic___at___Lean_Meta_subst_substEq_spec__0(x_45, x_3, x_4, x_5, x_6, x_39);
return x_46;
}
else
{
lean_object* x_47; uint8_t x_48; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_47 = lean_ctor_get(x_38, 0);
lean_inc(x_47);
lean_dec(x_38);
x_48 = !lean_is_exclusive(x_36);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_36, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
lean_ctor_set(x_36, 0, x_50);
return x_36;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_dec(x_36);
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_dec(x_47);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_36);
if (x_54 == 0)
{
return x_36;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_36, 0);
x_56 = lean_ctor_get(x_36, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_36);
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
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_13);
if (x_58 == 0)
{
return x_13;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_13, 0);
x_60 = lean_ctor_get(x_13, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_13);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_8);
if (x_62 == 0)
{
return x_8;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_8, 0);
x_64 = lean_ctor_get(x_8, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_8);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___Lean_Meta_splitIfTarget_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_24; 
x_7 = l_Lean_Meta_saveState___redArg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_3);
x_24 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5, x_26);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_8);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
return x_24;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
x_35 = l_Lean_Exception_isInterrupt(x_33);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = l_Lean_Exception_isRuntime(x_33);
x_10 = x_24;
x_11 = x_33;
x_12 = x_34;
x_13 = x_36;
goto block_23;
}
else
{
x_10 = x_24;
x_11 = x_33;
x_12 = x_34;
x_13 = x_35;
goto block_23;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_24, 0);
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_24);
lean_inc(x_38);
lean_inc(x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Exception_isInterrupt(x_37);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = l_Lean_Exception_isRuntime(x_37);
x_10 = x_39;
x_11 = x_37;
x_12 = x_38;
x_13 = x_41;
goto block_23;
}
else
{
x_10 = x_39;
x_11 = x_37;
x_12 = x_38;
x_13 = x_40;
goto block_23;
}
}
}
block_23:
{
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_10);
x_14 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5, x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___Lean_Meta_splitIfTarget_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_commitWhenSome_x3f___at___Lean_Meta_splitIfTarget_x3f_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_12; 
lean_inc(x_1);
x_12 = l_Lean_MVarId_getType(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Meta_SplitIf_splitIfAt_x3f(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_18 = x_16;
} else {
 lean_dec_ref(x_16);
 x_18 = lean_box(0);
}
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
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_23 = x_17;
} else {
 lean_dec_ref(x_17);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_24);
x_27 = l_Lean_Meta_simpIfTarget(x_24, x_26, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_25);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_30);
x_32 = l_Lean_Meta_simpIfTarget(x_30, x_31, x_3, x_4, x_5, x_6, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_44; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_44 = lean_name_eq(x_24, x_28);
lean_dec(x_24);
if (x_44 == 0)
{
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_43;
}
else
{
uint8_t x_45; 
x_45 = lean_name_eq(x_30, x_33);
lean_dec(x_30);
if (x_45 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_43;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_35);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
x_46 = lean_mk_string_unchecked("split", 5, 5);
x_47 = lean_mk_string_unchecked("failure", 7, 7);
x_48 = l_Lean_Name_mkStr2(x_46, x_47);
lean_inc(x_48);
x_49 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_48, x_3, x_4, x_5, x_6, x_34);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_48);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_8 = x_52;
goto block_11;
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_54 = lean_ctor_get(x_49, 1);
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
x_56 = lean_mk_string_unchecked("`split` tactic failed to simplify target using new hypotheses Goals:\n", 69, 69);
x_57 = l_Lean_stringToMessageData(x_56);
lean_dec(x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_28);
lean_ctor_set_tag(x_49, 7);
lean_ctor_set(x_49, 1, x_58);
lean_ctor_set(x_49, 0, x_57);
x_59 = lean_mk_string_unchecked("\n", 1, 1);
x_60 = l_Lean_stringToMessageData(x_59);
lean_dec(x_59);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_49);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_33);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_mk_string_unchecked("", 0, 0);
x_65 = l_Lean_stringToMessageData(x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_48, x_66, x_3, x_4, x_5, x_6, x_54);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_8 = x_68;
goto block_11;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_69 = lean_ctor_get(x_49, 1);
lean_inc(x_69);
lean_dec(x_49);
x_70 = lean_mk_string_unchecked("`split` tactic failed to simplify target using new hypotheses Goals:\n", 69, 69);
x_71 = l_Lean_stringToMessageData(x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_28);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_mk_string_unchecked("\n", 1, 1);
x_75 = l_Lean_stringToMessageData(x_74);
lean_dec(x_74);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_33);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_mk_string_unchecked("", 0, 0);
x_80 = l_Lean_stringToMessageData(x_79);
lean_dec(x_79);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_48, x_81, x_3, x_4, x_5, x_6, x_69);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_8 = x_83;
goto block_11;
}
}
}
}
block_43:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_dec(x_21);
if (lean_is_scalar(x_20)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_20;
}
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_dec(x_22);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_38);
if (lean_is_scalar(x_23)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_23;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
if (lean_is_scalar(x_18)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_18;
}
lean_ctor_set(x_41, 0, x_40);
if (lean_is_scalar(x_35)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_35;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_34);
return x_42;
}
}
else
{
uint8_t x_84; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_84 = !lean_is_exclusive(x_32);
if (x_84 == 0)
{
return x_32;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_32, 0);
x_86 = lean_ctor_get(x_32, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_32);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_88 = !lean_is_exclusive(x_27);
if (x_88 == 0)
{
return x_27;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_27, 0);
x_90 = lean_ctor_get(x_27, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_27);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
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
return x_15;
}
}
else
{
uint8_t x_92; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_12);
if (x_92 == 0)
{
return x_12;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_12, 0);
x_94 = lean_ctor_get(x_12, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_12);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfTarget_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_splitIfTarget_x3f___lam__0), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_commitWhenSome_x3f___at___Lean_Meta_splitIfTarget_x3f_spec__0___redArg(x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_14; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = lean_infer_type(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Meta_SplitIf_splitIfAt_x3f(x_2, x_15, x_3, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_26 = x_18;
} else {
 lean_dec_ref(x_18);
 x_26 = lean_box(0);
}
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_30 = x_25;
} else {
 lean_dec_ref(x_25);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_31);
x_32 = l_Lean_Meta_simpIfLocalDecl(x_31, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
lean_dec(x_29);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_35);
x_36 = l_Lean_Meta_simpIfLocalDecl(x_35, x_4, x_5, x_6, x_7, x_8, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_83; 
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
x_83 = lean_name_eq(x_31, x_33);
lean_dec(x_31);
if (x_83 == 0)
{
lean_dec(x_35);
x_40 = x_83;
goto block_82;
}
else
{
uint8_t x_84; 
x_84 = lean_name_eq(x_35, x_37);
lean_dec(x_35);
x_40 = x_84;
goto block_82;
}
block_82:
{
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_30)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_30;
}
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_37);
if (lean_is_scalar(x_26)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_26;
}
lean_ctor_set(x_42, 0, x_41);
if (lean_is_scalar(x_39)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_39;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_26);
x_44 = lean_mk_string_unchecked("split", 5, 5);
x_45 = lean_mk_string_unchecked("failure", 7, 7);
x_46 = l_Lean_Name_mkStr2(x_44, x_45);
lean_inc(x_46);
x_47 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_46, x_5, x_6, x_7, x_8, x_38);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_10 = x_50;
goto block_13;
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_52 = lean_ctor_get(x_47, 1);
x_53 = lean_ctor_get(x_47, 0);
lean_dec(x_53);
x_54 = lean_mk_string_unchecked("`split` tactic failed to simplify target using new hypotheses Goals:\n", 69, 69);
x_55 = l_Lean_stringToMessageData(x_54);
lean_dec(x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_33);
lean_ctor_set_tag(x_47, 7);
lean_ctor_set(x_47, 1, x_56);
lean_ctor_set(x_47, 0, x_55);
x_57 = lean_mk_string_unchecked("\n", 1, 1);
x_58 = l_Lean_stringToMessageData(x_57);
lean_dec(x_57);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_47);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_37);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_mk_string_unchecked("", 0, 0);
x_63 = l_Lean_stringToMessageData(x_62);
lean_dec(x_62);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_46, x_64, x_5, x_6, x_7, x_8, x_52);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_10 = x_66;
goto block_13;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_67 = lean_ctor_get(x_47, 1);
lean_inc(x_67);
lean_dec(x_47);
x_68 = lean_mk_string_unchecked("`split` tactic failed to simplify target using new hypotheses Goals:\n", 69, 69);
x_69 = l_Lean_stringToMessageData(x_68);
lean_dec(x_68);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_33);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_mk_string_unchecked("\n", 1, 1);
x_73 = l_Lean_stringToMessageData(x_72);
lean_dec(x_72);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_37);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_mk_string_unchecked("", 0, 0);
x_78 = l_Lean_stringToMessageData(x_77);
lean_dec(x_77);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_46, x_79, x_5, x_6, x_7, x_8, x_67);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_10 = x_81;
goto block_13;
}
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_85 = !lean_is_exclusive(x_36);
if (x_85 == 0)
{
return x_36;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_36, 0);
x_87 = lean_ctor_get(x_36, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_36);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_89 = !lean_is_exclusive(x_32);
if (x_89 == 0)
{
return x_32;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_32, 0);
x_91 = lean_ctor_get(x_32, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_32);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_93 = !lean_is_exclusive(x_17);
if (x_93 == 0)
{
return x_17;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_17, 0);
x_95 = lean_ctor_get(x_17, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_17);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_14);
if (x_97 == 0)
{
return x_14;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_14, 0);
x_99 = lean_ctor_get(x_14, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_14);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
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
LEAN_EXPORT lean_object* l_Lean_Meta_splitIfLocalDecl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_9 = l_Lean_Expr_fvar___override(x_2);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_splitIfLocalDecl_x3f___lam__0), 9, 4);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___boxed), 8, 3);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_10);
x_12 = l_Lean_commitWhenSome_x3f___at___Lean_Meta_splitIfTarget_x3f_spec__0___redArg(x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_SplitIf___hyg_3743_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_2 = lean_mk_string_unchecked("Meta", 4, 4);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("splitIf", 7, 7);
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
x_11 = lean_mk_string_unchecked("initFn", 6, 6);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("_@", 2, 2);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = l_Lean_Name_str___override(x_14, x_8);
x_16 = l_Lean_Name_str___override(x_15, x_2);
x_17 = l_Lean_Name_str___override(x_16, x_3);
x_18 = lean_mk_string_unchecked("SplitIf", 7, 7);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("_hyg", 4, 4);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_unsigned_to_nat(3743u);
x_23 = l_Lean_Name_num___override(x_21, x_22);
x_24 = lean_unbox(x_6);
x_25 = l_Lean_registerTraceClass(x_5, x_24, x_23, x_1);
return x_25;
}
}
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_SplitIf(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Cases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_SplitIf___hyg_3743_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
